/*
 * Franklin Wei
 * 19 May 2018
 * yaCAS - "Yet Another Computer Algebra System"
 *
 * This is a program to manipulate algebraic expressions. It features
 * a way of representing arbitrary expressions in memory, a parser to
 * convert to and from standard mathematical notation, and functions
 * to simplify, differentiate, and integrate such
 * expressions. Additionally, it can function as a simple numerical
 * calculator.
 *
 * Expressions are represented by an abstract syntax tree, a node of
 * which is represented by a "struct expression" object (see
 * definition below). Expressions are passed by reference to most
 * functions, but most functions will allocate an entirely new
 * expression tree to return their results. This results in a not
 * insignificant amount of overhead as memory allocations and frees
 * take place, but also greatly simplifies the memory model.
 *
 * Variables are supported through a simple hash map. Strings are
 * mapped to expression trees through the "struct variable" object,
 * and the expression trees are then substituted into the computation
 * as needed. There is a special variable called . that stores the
 * result of the previous computation.
 *
 * Differentiation is performed recursively on the expression
 * tree. The differentiation of most expressions is performed by
 * recursing down the tree, applying the basic rules of
 * differentiation to combine the derivatives of child nodes. See the
 * "diff" function for implementation.
 *
 * The expression parser is rather limited when it comes to
 * tokenization. In its current form, it relies on tokens in the
 * expression, say, "x ^ 2", being separated with spaces. That is,
 * typing an expression like "x^2", without spaces between tokens,
 * will result in undesired behavior (in this case, the parser wil
 * view the token "x^2" as a variable name, not an expression). Just
 * be sure to always separate tokens with a space, and all will be
 * well.
 *
 * Finally, when using the exponential function, the form "exp ( x )"
 * is preferred over "e ^ x", since the parser will recognize exp() as
 * a special function and know about its special properties, while e^x
 * will be treated as some constant raised to a power, without the
 * special features of the exp() being recognized.
 *
 * Please note that this is a work in progress. The simplification,
 * equality checking, and integration algorithms used are rudimentary
 * at best, although differentiation should be relatively robust.
 *
 * Usage instructions: compile with no optimization, as this may cause
 * undefined behavior, and link with -lm and -lreadline:
 *
 *    cc -O0 yacas.c -o yacas -lm -lreadline
 *
 * Then run with no arguments and you should be presented with a
 * "yaCAS> " prompt. From here, you can type "help" at the command
 * line for an overview of the basic syntax.
 *
 * Readline can be disabled by commenting out the #define below (in
 * which case the getline() function will be used instead):
 */

#define USE_READLINE

#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <setjmp.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#ifdef USE_READLINE
#include <readline/readline.h>
#include <readline/history.h>
#endif

/* tool for manipulating algebraic expressions */

/* packed to save memory with large expressions */
struct expression {
    char type; /* T_* */
    union {
        double constant; /* T_CONST */
        char *varname; /* T_VAR, dynamically allocated */
        struct {
            char op; /* OP_* */
            struct expression *left, *right;
        } subexpr; /* T_SUBEXPR */
        struct {
            char fn /* FN_* */;
            struct expression *operand, *operand2;
        } specfunc; /* T_SPECFUNC */
    };
} __attribute__((packed));

enum { OP_POW = 0, OP_MUL, OP_DIV, OP_ADD, OP_SUB, OP_DIFF, OP_INT, OP_ASSIGN, OP_EQUALS, OP_LAST, /* not a real operator: */ OP_LPAREN };
enum { T_CONST = 0, T_VAR, T_SUBEXPR, T_SPECFUNC };
enum { FN_LOG = 0, FN_EXP, FN_SIN, FN_COS, FN_TAN, FN_CSC, FN_SEC, FN_COT, FN_ASIN, FN_ACOS, FN_ATAN, FN_ACSC, FN_ASEC, FN_ACOT, FN_ABS, FN_NEGATE, FN_SQRT, FN_LAST };
enum { RIGHT, LEFT };

const char *op_names[] = {
    "^", "*", "/", "+", "-", "diff", "int", "=", "==", "none", "("
};

const char *type_names[] = {
    "constant", "variable", "expression", "function", "null"
};

const int op_assoc[] = {
    RIGHT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT
};

const bool op_commutative[] = {
    false, true, false, true, false, false, false, true
};

const char *fn_names[] = {
    "log", "exp", "sin", "cos", "tan", "csc", "sec", "cot", "asin", "acos", "atan", "acsc", "asec", "acot", "abs", "-", "sqrt"
};

bool is_constant(struct expression *expr);
bool is_constvar(const char *name);
bool is_var(const char *name);
bool check_boolean(const char *varname);
double eval_numexpr(struct expression *expr);
double eval_numexpr_and_free(struct expression *expr);
struct expression *diff(struct expression *expr, const char *var);
struct expression *integrate(struct expression *expr, const char *var);
struct expression *dup_expr(struct expression *expr);
struct expression *eval_expr(struct expression *expr);
struct expression *simp(struct expression *expr);
void print_expr(struct expression *expr);
void setvar(const char *name, struct expression *value, bool constant);

bool simp_progress = false;
bool memdiag = false;
bool interactive = true;
bool vars_ok = true;

jmp_buf restore;

void __attribute__((noreturn)) fail(const char *msg)
{
    fprintf(stderr, "%s\n", msg);
    longjmp(restore, 1);
}

void __attribute__((noreturn)) fatal(const char *msg)
{
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

int memusage = 0, peakmem = 0;

#define MAX_MEMUSAGE 512*1024*1024

void check_mem(void)
{
    if(memusage > MAX_MEMUSAGE)
        fatal("OOM");
    if(memusage > peakmem)
        peakmem = memusage;
}

struct expression *new_var(const char *varname)
{
    struct expression *new = calloc(1, sizeof(*new));
    new->type = T_VAR;
    new->varname = strdup(varname);
    memusage += sizeof(*new);
    check_mem();
    if(check_boolean("memdiag"))
        printf("new var %p = %s\n", new, varname);
    return new;
}

struct expression *new_const(double x)
{
    struct expression *new = calloc(1, sizeof(*new));
    new->type = T_CONST;
    new->constant = x;
    memusage += sizeof(*new);
    check_mem();
    if(check_boolean("memdiag"))
        printf("new const %p = %g\n", new, x);
    return new;
}

struct expression *new_op(int op, struct expression *l, struct expression *r)
{
    struct expression *new = calloc(1, sizeof(*new));
    new->type = T_SUBEXPR;
    new->subexpr.op = op;
    new->subexpr.left = l;
    new->subexpr.right = r;
    memusage += sizeof(*new);
    check_mem();
    if(check_boolean("memdiag"))
        printf("new op %p %s\n", new, op_names[(int)op]);
    return new;
}

struct expression *new_specfunc(int fn, struct expression *expr)
{
    struct expression *new = calloc(1, sizeof(*new));
    new->type = T_SPECFUNC;
    new->specfunc.fn = fn;
    new->specfunc.operand = expr;
    memusage += sizeof(*new);
    if(check_boolean("memdiag"))
        printf("new specfunc %p %s\n", new, fn_names[(int)fn]);
    return new;
}

int expr_prec(struct expression expr)
{
    switch(expr.type)
    {
    case T_CONST:
    case T_VAR:
    case T_SPECFUNC:
        return 10;
    case T_SUBEXPR:
        switch(expr.subexpr.op)
        {
        case OP_LPAREN:
            return -1; /* must be lowest */
        case OP_ASSIGN:
            return 0;
        case OP_EQUALS:
            return 1;
        case OP_DIFF:
        case OP_INT:
            return 2;
        case OP_ADD:
        case OP_SUB:
            return 3;
        case OP_MUL:
        case OP_DIV:
            return 4;
        case OP_POW:
            return 5;
        default:
            fatal("fall through");
        }
    default:
        fatal("fall through");
    }
}

void free_expr(struct expression *expr)
{
    if(expr)
    {
        switch(expr->type)
        {
        case T_SUBEXPR:
            free_expr(expr->subexpr.left);
            free_expr(expr->subexpr.right);
            break;
        case T_SPECFUNC:
            free_expr(expr->specfunc.operand);
            break;
        case T_VAR:
            free(expr->varname);
            break;
        default:
            break;
        }
        memusage -= sizeof(struct expression);
        if(check_boolean("memdiag"))
            printf("freeing %p\n", expr);
        free(expr);
    }
}

struct expression *eval_and_free(struct expression *expr)
{
    struct expression *ret = eval_expr(expr);
    free_expr(expr);
    return ret;
}

struct expression *simp_and_free(struct expression *expr)
{
    struct expression *ret = simp(expr);
    free_expr(expr);
    return ret;
}

struct expression *diff_and_free(struct expression *expr, const char *var)
{
    struct expression *ret = diff(expr, var);
    free_expr(expr);
    return ret;
}

struct expression *integrate_and_free(struct expression *expr, const char *var)
{
    struct expression *ret = integrate(expr, var);
    free_expr(expr);
    return ret;
}

/* simplify as much as possible, while freeing original */
struct expression *simp_and_free_max(struct expression *expr)
{
    do {
        simp_progress = false;
        expr = simp_and_free(expr);
    } while(simp_progress);
    return expr;
}

bool is_muldiv(struct expression *expr)
{
    return expr->type == T_SUBEXPR && (expr->subexpr.op == OP_MUL || expr->subexpr.op == OP_DIV);
}

/* returns true iff expr or a subexpr depends on varname in some way */
bool expr_references(struct expression *expr, const char *varname)
{
    switch(expr->type)
    {
    case T_CONST:
        return false;
    case T_VAR:
        return !strcmp(expr->varname, varname);
    case T_SUBEXPR:
        return expr_references(expr->subexpr.left, varname) || expr_references(expr->subexpr.right, varname);
    case T_SPECFUNC:
        return expr_references(expr->specfunc.operand, varname);
    default:
        fatal("fall through");
    }
}

/* simple stuff, doesn't always work */
bool expr_equals(struct expression *l, struct expression *r)
{
    /* first the low-hanging fruit */
    if(l == r)
        return true;

    /* duplicate them first so we can modify them if need be */
    l = dup_expr(l);
    r = dup_expr(r);

    l = simp_and_free_max(l);
    r = simp_and_free_max(r);

    /* must come after simplification */
    if(is_constant(l) && is_constant(r))
        return eval_numexpr_and_free(l) == eval_numexpr_and_free(r);

    /* not foolproof */
    if(l->type != r->type)
    {
        free_expr(l);
        free_expr(r);
        return false;
    }

    bool ret = false;

    switch(l->type)
    {
    case T_SUBEXPR:
        if(l->subexpr.op == r->subexpr.op &&
           ((expr_equals(l->subexpr.left, r->subexpr.left) && expr_equals(l->subexpr.right, r->subexpr.right)) ||
            (op_commutative[l->subexpr.op] &&
             expr_equals(l->subexpr.left, r->subexpr.right) && expr_equals(l->subexpr.right, r->subexpr.left))))
            ret = true;
        else
            ret = false;

        free_expr(l);
        free_expr(r);
        return ret;
    case T_SPECFUNC:
        ret = l->specfunc.fn == r->specfunc.fn && expr_equals(l->specfunc.operand, r->specfunc.operand);
        free_expr(l);
        free_expr(r);
        return ret;
    case T_VAR:
        /* symbolic comparison */
        if(!is_var(l->varname) && !is_var(r->varname))
        {
            ret = !strcmp(l->varname, r->varname);
            free_expr(l);
            free_expr(r);
            return ret;
        }
        break;
    default:
        break;
    }

    /* try evaluating them and recurse */
    l = eval_and_free(l);
    r = eval_and_free(r);

    ret = expr_equals(l, r);

    free_expr(l);
    free_expr(r);

    return ret;
}

#define VARMAP_SIZE 20

/* chained hash map */
struct variable {
    char *name; /* dynamic */
    struct expression *value;
    bool constant;
    struct variable *next;
} *varmap[VARMAP_SIZE];

uint32_t var_hash(const char *str)
{
    uint32_t hash = 5381;
    char c;
    while((c = *str++))
    {
        hash = ((hash << 5) + hash) ^ c;
    }

    return hash;
}

bool is_constvar(const char *name)
{
    uint32_t idx = var_hash(name) % VARMAP_SIZE;

    struct variable *i = varmap[idx];
    while(i)
    {
        if(!strcmp(i->name, name))
            return i->constant;
        i = i->next;
    }

    return false;
}

/* value must be persistent, but name doesn't need to be */
void setvar(const char *name, struct expression *value, bool constant)
{
    uint32_t idx = var_hash(name) % VARMAP_SIZE;

    struct variable *old, *i = varmap[idx];
    old = i;
    while(i)
    {
        if(!strcmp(i->name, name))
        {
            /* free old value */
            free_expr(i->value);
            i->value = value;
            return;
        }
        i = i->next;
    }

    /* not found, insert as first element in chain */
    struct variable *newvar = calloc(1, sizeof(struct variable));
    newvar->name = strdup(name);
    newvar->constant = constant;
    newvar->next = old;
    newvar->value = value;

    varmap[idx] = newvar;
}

void dumpvars(void)
{
    for(int idx = 0; idx < VARMAP_SIZE; ++idx)
    {
        struct variable *i = varmap[idx];
        while(i)
        {
            printf("%s = ", i->name);
            print_expr(i->value);
            printf("(%s)\n", type_names[(int)i->value->type]);
            i = i->next;
        }
    }
}

void freevars(void)
{
    /* can no longer access vars */
    vars_ok = false;

    for(int idx = 0; idx < VARMAP_SIZE; ++idx)
    {
        struct variable *i = varmap[idx];
        while(i)
        {
            free_expr(i->value);
            free(i->name);
            struct variable *next = i->next;
            free(i);
            i = next;
        }
    }
}

void sigint(int sig)
{
    freevars();
}

bool is_var(const char *name)
{
    uint32_t idx = var_hash(name) % VARMAP_SIZE;

    struct variable *i = varmap[idx];

    while(i)
    {
        if(!strcmp(i->name, name))
            return true;
        i = i->next;
    }

    return false;
}

struct expression *getvar(const char *name)
{
    uint32_t idx = var_hash(name) % VARMAP_SIZE;

    struct variable *i = varmap[idx];
    while(i)
    {
        if(!strcmp(i->name, name))
            return i->value;
        i = i->next;
    }

    return NULL;
}

bool delvar(const char *name)
{
    uint32_t idx = var_hash(name) % VARMAP_SIZE;

    struct variable *i = varmap[idx], *last = NULL;

    while(i)
    {
        if(!strcmp(i->name, name))
        {
            if(last)
                last->next = i->next;
            else
                varmap[idx] = NULL;
            free_expr(i->value);
            free(i->name);
            free(i);
            return true;
        }
        last = i;
        i = i->next;
    }

    return false;
}

/* check whether a variable is nonzero without any intermediate functions */
bool check_boolean(const char *varname)
{
    if(!vars_ok)
        return false;
    struct expression *expr = getvar(varname);
    if(!expr)
        return false;
    switch(expr->type)
    {
    case T_CONST:
        return expr->constant == 1;
    default:
        return false;
    }
}

bool is_constant(struct expression *expr)
{
    switch(expr->type)
    {
    case T_CONST:
        return true;
    case T_VAR:
        /* see if there is an expression corresponding to var */
        if(is_var(expr->varname))
            return is_constant(getvar(expr->varname));

        /* unknown, assume false */
        return false;
    case T_SUBEXPR:
        return is_constant(expr->subexpr.left) && is_constant(expr->subexpr.right);
    case T_SPECFUNC:
        return is_constant(expr->specfunc.operand);
    default:
        fatal("fall through");
    }
}

/* returns true if expr is a constant multiple of some variable (if
 * the variable is not a constant, it will be evaluated recursively) */
bool is_constant_mult(struct expression *expr, double *coef, const char **varname)
{
    switch(expr->type)
    {
    case T_CONST:
        return false;
    case T_VAR:
        if(is_var(expr->varname))
            return is_constant_mult(getvar(expr->varname), coef, varname);
        *coef = 1;
        *varname = expr->varname;
        return true;
    case T_SUBEXPR:
        switch(expr->subexpr.op)
        {
        case OP_MUL:
            break;
        }
    case T_SPECFUNC:
        return false;
    }
}

struct expression *dup_expr(struct expression *expr)
{
    switch(expr->type)
    {
    case T_CONST:
        return new_const(expr->constant);
    case T_VAR:
        return new_var(expr->varname);
    case T_SUBEXPR:
        return new_op(expr->subexpr.op, dup_expr(expr->subexpr.left), dup_expr(expr->subexpr.right));
    case T_SPECFUNC:
        return new_specfunc(expr->specfunc.fn, dup_expr(expr->specfunc.operand));
    default:
        fatal("fall through");
    }
}

double eval_specfunc(int fn, double x)
{
    switch(fn)
    {
    case FN_LOG:
        return log(x);
    case FN_EXP:
        return exp(x);
    case FN_SIN:
        return sin(x);
    case FN_COS:
        return cos(x);
    case FN_TAN:
        return tan(x);
    case FN_CSC:
        return 1 / sin(x);
    case FN_SEC:
        return 1 / cos(x);
    case FN_COT:
        return 1 / tan(x);
    case FN_ASIN:
        return asin(x);
    case FN_ACOS:
        return acos(x);
    case FN_ATAN:
        return atan(x);
    case FN_ACSC:
        return asin(1/x);
    case FN_ASEC:
        return acos(1/x);
    case FN_ACOT:
        return atan(1/x);
    case FN_ABS:
        return fabs(x);
    case FN_NEGATE:
        return -x;
    case FN_SQRT:
        return sqrt(x);
    default:
        fatal("fall through");
    }
}

struct expression *eval_op(int op, struct expression *lexpr, struct expression *rexpr)
{
    if(op == OP_DIFF)
    {
        /* allow for syntax in the form f diff x = 2 for evaluating
         * the derivative at x = 2 */
        switch(rexpr->type)
        {
        case T_VAR:
            return diff_and_free(eval_expr(lexpr), rexpr->varname);
        case T_SUBEXPR:
            if(rexpr->subexpr.op == OP_ASSIGN && rexpr->subexpr.left->type == T_VAR && is_constant(rexpr->subexpr.right))
            {
                bool have_old = is_var(rexpr->subexpr.left->varname);

                struct expression *old = NULL;

                /* save state */
                if(have_old)
                {
                    old = dup_expr(getvar(rexpr->subexpr.left->varname));
                    /* delete so it's not a constant */
                    delvar(rexpr->subexpr.left->varname);
                }

                /* get derivative */
                struct expression *deriv = diff_and_free(eval_expr(lexpr), rexpr->subexpr.left->varname);

                /* set variable (duplicate because setvar frees it later */
                setvar(rexpr->subexpr.left->varname, dup_expr(rexpr->subexpr.right), false);

                double val = eval_numexpr_and_free(deriv);

                /* restore */
                if(have_old)
                    setvar(rexpr->subexpr.left->varname, old, false);
                else
                    delvar(rexpr->subexpr.left->varname);

                return new_const(val);
            }
            /* fall through */
        default:
            fail("diff operator must take variable as second operand");
        }
    }
    else if(op == OP_INT)
    {
        struct expression *result = integrate_and_free(eval_expr(lexpr), rexpr->varname);
        if(!result)
            return new_op(op, dup_expr(lexpr), dup_expr(rexpr));
    }
    else if(op == OP_ASSIGN)
    {
        if(lexpr->type != T_VAR)
            fail("assignment requires variable as first operand");
        if(is_constvar(lexpr->varname))
            fail("cannot change constant value");
        if(expr_references(rexpr, lexpr->varname))
            fail("circular reference");

        setvar(lexpr->varname, dup_expr(rexpr), false);
        return dup_expr(rexpr);
    }
    else if(op == OP_EQUALS)
    {
        /* booleans are just 1 or 0 */
        return new_const(expr_equals(rexpr, lexpr));
    }
    else
    {
        if(!(is_constant(lexpr) && is_constant(rexpr)))
        {
            return new_op(op, dup_expr(lexpr), dup_expr(rexpr));
        }

        double l = eval_numexpr(lexpr), r = eval_numexpr(rexpr);
        double ret = 0;

        switch(op)
        {
        case OP_ADD:
            ret = l + r;
            break;
        case OP_SUB:
            ret = l - r;
            break;
        case OP_MUL:
            ret = l * r;
            break;
        case OP_DIV:
            ret = l / r;
            break;
        case OP_POW:
            ret = pow(l, r);
            break;
        default:
            fail("fall through");
        }
        return new_const(ret);
    }
}

/* evaluate constants and execute any operators */
struct expression *eval_expr(struct expression *expr)
{
    switch(expr->type)
    {
    case T_CONST:
        return new_const(expr->constant);
    case T_VAR:
        /* this could fail upon a circular reference */
        if(is_var(expr->varname))
            return eval_expr(getvar(expr->varname));

        /* otherwise keep it symbolic */
        return new_var(expr->varname);
    case T_SUBEXPR:
        return eval_op(expr->subexpr.op, expr->subexpr.left, expr->subexpr.right);
    case T_SPECFUNC:
        if(!is_constant(expr->specfunc.operand))
            return new_specfunc(expr->specfunc.fn, eval_expr(expr->specfunc.operand));
        return new_const(eval_specfunc(expr->specfunc.fn, eval_numexpr(expr->specfunc.operand)));
    default:
        fail("falll through");
    }
}

double eval_numexpr(struct expression *expr)
{
    struct expression *result = eval_expr(expr);
    double x;
    switch(result->type)
    {
    case T_CONST:
        x = result->constant;
        break;
    case T_VAR:
        x = eval_numexpr(getvar(expr->varname));
        break;
    default:
        free_expr(result);
        fail("attempted to evaluate a non-numeric expression");
    }
    free_expr(result);
    return x;
}

double eval_numexpr_and_free(struct expression *expr)
{
    double ret = eval_numexpr(expr);
    free_expr(expr);
    return ret;
}

/* returns an entirely new expression object */
struct expression *simp(struct expression *expr)
{
    if(is_constant(expr))
        return new_const(eval_numexpr(expr));

    switch(expr->type)
    {
    case T_VAR:
        return dup_expr(expr);
    case T_SUBEXPR:
        switch(expr->subexpr.op)
        {
        case OP_ADD:
        case OP_SUB:
            /* cannot simplify 0 - b to b */
            if(is_constant(expr->subexpr.left) && eval_numexpr(expr->subexpr.left) == 0)
            {
                simp_progress = true;
                if(expr->subexpr.op == OP_ADD)
                    return simp(expr->subexpr.right);
                else
                    return new_specfunc(FN_NEGATE, simp(expr->subexpr.right));
            }
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 0)
            {
                simp_progress = true;
                return simp(expr->subexpr.left);
            }
            if(expr_equals(expr->subexpr.left, expr->subexpr.right))
            {
                simp_progress = true;
                if(expr->subexpr.op == OP_SUB)
                    return new_const(0);
                return new_op(OP_MUL,
                              new_const(2),
                              simp(expr->subexpr.left));
            }
            return new_op(expr->subexpr.op, simp(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_MUL:
            if((is_constant(expr->subexpr.left) && eval_numexpr(expr->subexpr.left) == 0) ||
               (is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 0))
            {
                simp_progress = true;
                return new_const(0);
            }
            if(is_constant(expr->subexpr.left) && eval_numexpr(expr->subexpr.left) == 1)
            {
                simp_progress = true;
                return simp(expr->subexpr.right);
            }
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 1)
            {
                simp_progress = true;
                return simp(expr->subexpr.left);
            }
            /* both cannot be constant, since that would have been caught earlier */
            if(is_constant(expr->subexpr.left) && is_muldiv(expr->subexpr.right))
            {
                if(is_constant(expr->subexpr.right->subexpr.left))
                {
                    simp_progress = true;
                    return new_op(expr->subexpr.op,
                                  new_const(eval_numexpr(expr->subexpr.left) * eval_numexpr(expr->subexpr.right->subexpr.left)),
                                  dup_expr(expr->subexpr.right->subexpr.right));
                }
                if(is_constant(expr->subexpr.right->subexpr.right))
                {
                    simp_progress = true;
                    if(expr->subexpr.right->subexpr.op == OP_MUL)
                    {
                        return new_op(OP_MUL,
                                      new_const(eval_numexpr(expr->subexpr.left) * eval_numexpr(expr->subexpr.right->subexpr.right)),
                                      dup_expr(expr->subexpr.right->subexpr.left));
                    }
                    else
                        return new_op(OP_MUL,
                                      new_const(eval_numexpr(expr->subexpr.left) / eval_numexpr(expr->subexpr.right->subexpr.right)),
                                      dup_expr(expr->subexpr.right->subexpr.left));
                }
            }

            if(is_constant(expr->subexpr.right) && is_muldiv(expr->subexpr.left))
            {
                if(is_constant(expr->subexpr.left->subexpr.left))
                {
                    simp_progress = true;
                    return new_op(expr->subexpr.op,
                                  new_const(eval_numexpr(expr->subexpr.right) * eval_numexpr(expr->subexpr.left->subexpr.left)),
                                  dup_expr(expr->subexpr.left->subexpr.right));
                }
                if(is_constant(expr->subexpr.left->subexpr.right))
                {
                    simp_progress = true;
                    if(expr->subexpr.left->subexpr.op == OP_MUL)
                    {
                        return new_op(OP_MUL,
                                      new_const(eval_numexpr(expr->subexpr.right) * eval_numexpr(expr->subexpr.left->subexpr.right)),
                                      dup_expr(expr->subexpr.left->subexpr.left));
                    }
                    else
                        return new_op(OP_MUL,
                                      new_const(eval_numexpr(expr->subexpr.right) / eval_numexpr(expr->subexpr.left->subexpr.right)),
                                      dup_expr(expr->subexpr.left->subexpr.left));
                }
            }
            return new_op(expr->subexpr.op, simp(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_DIV:
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 1)
            {
                simp_progress = true;
                return simp(expr->subexpr.left);
            }
            if(expr_equals(expr->subexpr.left, expr->subexpr.right))
            {
                simp_progress = true;
                return new_const(1);
            }
            return new_op(expr->subexpr.op, simp(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_POW:
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 0)
            {
                simp_progress = true;
                return new_const(1);
            }
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == .5)
            {
                simp_progress = true;
                return new_specfunc(FN_SQRT, simp(expr->subexpr.left));
            }
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) == 1)
            {
                simp_progress = true;
                return simp(expr->subexpr.left);
            }
#if 0
            if(is_constant(expr->subexpr.right) && eval_numexpr(expr->subexpr.right) < 0)
            {
                simp_progress = true;
                return new_op(OP_DIV,
                              new_const(1),
                              new_op(OP_POW,
                                     simp(expr->subexpr.left),
                                     new_const(-eval_numexpr(expr->subexpr.right))));
            }
#endif
            if(expr->subexpr.left->type == T_SUBEXPR && expr->subexpr.left->subexpr.op == OP_POW && is_constant(expr->subexpr.left->subexpr.right) && is_constant(expr->subexpr.right))
            {
                simp_progress = true;
                return new_op(OP_POW, simp(expr->subexpr.left->subexpr.left), new_const(eval_numexpr(expr->subexpr.left->subexpr.right) * eval_numexpr(expr->subexpr.right)));
            }
            return new_op(expr->subexpr.op, simp(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_DIFF:
            return new_op(OP_DIFF, simp(expr->subexpr.left), dup_expr(expr->subexpr.right));
        case OP_INT:
            return new_op(OP_INT, simp(expr->subexpr.left), dup_expr(expr->subexpr.right));
        case OP_ASSIGN:
            return new_op(OP_ASSIGN, dup_expr(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_EQUALS:
            return new_op(OP_EQUALS, dup_expr(expr->subexpr.left), dup_expr(expr->subexpr.right));
        default:
            fatal("fall through");
        }
        break;
    case T_SPECFUNC:
        switch(expr->specfunc.fn)
        {
        case FN_NEGATE:
            if(is_constant(expr->specfunc.operand))
            {
                double val = eval_numexpr(expr->specfunc.operand);
                if(val < 0)
                    return new_const(-val);
            }
            /* fall through */
        default:
            return new_specfunc(expr->specfunc.fn, simp(expr->specfunc.operand));
        }
    default:
        fatal("fall through");
    }
}

/* integrate with respect to "var", treating all other variables as
 * CONSTANTS; probably won't work (in which case it will return NULL) */
struct expression *integrate(struct expression *expr, const char *var)
{
    if(is_constant(expr))
        return new_op(OP_MUL, new_const(eval_numexpr(expr)), new_var(var));

    switch(expr->type)
    {
    case T_CONST:
        return new_op(OP_MUL, new_const(expr->constant), new_var(var));
    case T_VAR:
        if(!strcmp(expr->varname, var))
            return new_op(OP_MUL,
                          new_const(.5),
                          new_op(OP_POW,
                                 new_var(var),
                                 new_const(2)));
        return new_op(OP_MUL, dup_expr(expr), new_var(var));
    case T_SUBEXPR:
        switch(expr->subexpr.op)
        {
        case OP_ADD:
        case OP_SUB:
        {
            /* first try integrating both operands */
            struct expression *lint = integrate(expr->subexpr.left, var);
            struct expression *rint = integrate(expr->subexpr.right, var);
            if(lint && rint)
                return new_op(expr->subexpr.op, integrate(expr->subexpr.left, var), integrate(expr->subexpr.right, var));

            free_expr(lint);
            free_expr(rint);

            /* fail */
            return NULL;
        }

        case OP_MUL:
        {
            /* first try integrating both operands */
            struct expression *lint = integrate(expr->subexpr.left, var);
            struct expression *rint = integrate(expr->subexpr.right, var);

            /* check for constant multiple */
            if(is_constant(expr->subexpr.left))
            {
                return rint ? new_op(OP_MUL,
                                     new_const(eval_numexpr(expr->subexpr.left)),
                                     rint) : rint;
            }
            if(is_constant(expr->subexpr.right))
            {
                return lint ? new_op(OP_MUL,
                                     new_const(eval_numexpr(expr->subexpr.right)),
                                     lint) : lint;
            }
            /* disabled */
#if 0
            /* parts */
            /* check if the expression is in the form u'*v and if we
             * can integrate u and u*v' */
            struct expression *intuvprime = integrate_and_free(simp_and_free(new_op(OP_MUL,
                                                                                    dup_expr(lint),
                                                                                    diff(expr->subexpr.right, var))),
                                                               var);
            if(lint && intuvprime)
            {
                return new_op(OP_SUB,
                              new_op(OP_MUL,
                                     lint,
                                     dup_expr(expr->subexpr.right)),
                              intuvprime);
            }
            free_expr(intuvprime);

            struct expression *intuprimev = integrate_and_free(simp_and_free(new_op(OP_MUL,
                                                                                    diff(expr->subexpr.left, var),
                                                                                    dup_expr(rint))),
                                                               var);
            if(rint && intuprimev)
            {
                return new_op(OP_SUB,
                              new_op(OP_MUL,
                                     dup_expr(expr->subexpr.left),
                                     rint),
                              intuprimev);
            }
            free_expr(intuprimev);
#endif
            free_expr(rint);
            free_expr(lint);

            return NULL;
        }
        case OP_POW:
            if(expr->subexpr.left->type == T_VAR && !strcmp(expr->subexpr.left->varname, var) && is_constant(expr->subexpr.right))
            {
                return new_op(OP_MUL,
                              new_op(OP_DIV,
                                     new_const(1),
                                     new_const(eval_numexpr(expr->subexpr.right) + 1)),
                              new_op(OP_POW,
                                     new_var(expr->subexpr.left->varname),
                                     new_const(eval_numexpr(expr->subexpr.right) + 1)));
            }
            /* fall through */
        default:
            return NULL;
        }
    case T_SPECFUNC:
    {
        switch(expr->specfunc.fn)
        {
        case FN_EXP:
            if(expr->specfunc.operand->type == T_VAR && !strcmp(expr->specfunc.operand->varname, var))
                return new_specfunc(FN_EXP, dup_expr(expr->specfunc.operand));
            /* fall through */
        default:
            break;
        }
        /* fall through */
    }
    default:
        return NULL;
    }
}

/* differentiate with respect to "var", returns entirely new object */
struct expression *diff(struct expression *expr, const char *var)
{
    switch(expr->type)
    {
    case T_CONST:
        return new_const(0);
    case T_VAR:
        if(!strcmp(var, expr->varname))
            return new_const(1);
        else
        {
            //if(is_constant(expr))
            //return new_const(0);
            if(is_var(expr->varname))
                return diff(eval_expr(expr), var);
            return new_op(OP_DIFF, dup_expr(expr), new_var(var));
        }
    case T_SUBEXPR:
        switch(expr->subexpr.op)
        {
        case OP_ADD:
        case OP_SUB:
            return simp_and_free(new_op(expr->subexpr.op, diff(expr->subexpr.left, var), diff(expr->subexpr.right, var)));
        case OP_MUL:
            /* f'g + fg' */
            return simp_and_free(new_op(OP_ADD,
                                        new_op(OP_MUL, diff(expr->subexpr.left, var), dup_expr(expr->subexpr.right)),
                                        new_op(OP_MUL, dup_expr(expr->subexpr.left), diff(expr->subexpr.right, var))));
        case OP_DIV:
            return simp_and_free(new_op(OP_DIV,
                                        new_op(OP_SUB,
                                               new_op(OP_MUL, diff(expr->subexpr.left, var), dup_expr(expr->subexpr.right)),
                                               new_op(OP_MUL, dup_expr(expr->subexpr.left), diff(expr->subexpr.right, var))),
                                        new_op(OP_POW, dup_expr(expr->subexpr.right), new_const(2))));
        case OP_POW:
            /* just n * f(x) ^ (n - 1) * f'(x) */
            if(is_constant(expr->subexpr.right))
            {
                return simp_and_free(new_op(OP_MUL,
                                            new_const(eval_numexpr(expr->subexpr.right)),
                                            new_op(OP_MUL,
                                                   new_op(OP_POW,
                                                          dup_expr(expr->subexpr.left),
                                                          new_op(OP_SUB,
                                                                 dup_expr(expr->subexpr.right),
                                                                 new_const(1))),
                                                   diff(expr->subexpr.left, var))));
            }
            else
            {
                /* f^(g-1) * (gf' + fg'ln(f)) */
                return simp_and_free(new_op(OP_MUL,
                                            new_op(OP_POW,
                                                   dup_expr(expr->subexpr.left),
                                                   new_op(OP_SUB,
                                                          dup_expr(expr->subexpr.right),
                                                          new_const(1))),
                                            new_op(OP_ADD,
                                                   new_op(OP_MUL,
                                                          dup_expr(expr->subexpr.right),
                                                          diff(expr->subexpr.left, var)),
                                                   new_op(OP_MUL,
                                                          dup_expr(expr->subexpr.left),
                                                          new_op(OP_MUL,
                                                                 diff(expr->subexpr.right, var),
                                                                 new_specfunc(FN_LOG, dup_expr(expr->subexpr.left)))))));
            }
        case OP_DIFF:
            return simp_and_free(new_op(OP_DIFF, dup_expr(expr), new_var(var)));
        case OP_INT:
            /* d/dx int f(x) dx = f(x) */
            if(expr->subexpr.right->type == T_VAR && !strcmp(expr->subexpr.right->varname, var))
                return simp(expr->subexpr.left);

            /* otherwise return nothing */
            return simp_and_free(new_op(OP_INT, dup_expr(expr), new_var(var)));
        case OP_ASSIGN:
            fail("cannot differentiate assignment operator (did you mean == ?)");
        case OP_EQUALS:
            return simp_and_free(new_op(OP_EQUALS, diff(expr->subexpr.left, var), diff(expr->subexpr.right, var)));
        default:
            fatal("fall through");
        }
    case T_SPECFUNC:
        switch(expr->specfunc.fn)
        {
        case FN_LOG:
            return simp_and_free(new_op(OP_DIV,
                                        diff(expr->specfunc.operand, var),
                                        dup_expr(expr->specfunc.operand)));
        case FN_EXP:
            return simp_and_free(new_op(OP_MUL,
                                        diff(expr->specfunc.operand, var),
                                        new_specfunc(FN_EXP, dup_expr(expr->specfunc.operand))));
        case FN_SIN:
            return simp_and_free(new_op(OP_MUL,
                          new_specfunc(FN_COS, dup_expr(expr->specfunc.operand)),
                                        diff(expr->specfunc.operand, var)));
        case FN_COS:
            return simp_and_free(new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 new_specfunc(FN_SIN, dup_expr(expr->specfunc.operand)),
                                 diff(expr->specfunc.operand, var))));
        case FN_TAN:
            return simp_and_free(new_op(OP_DIV,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_POW,
                                 new_specfunc(FN_COS,
                                              dup_expr(expr->specfunc.operand)),
                                 new_const(2))));
        case FN_CSC:
            return simp_and_free(new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 diff(expr->specfunc.operand, var),
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_const(1),
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2))),
                                        new_const(-.5)))));
        case FN_SEC:
            return simp_and_free(new_op(OP_MUL,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_POW,
                                 new_op(OP_SUB,
                                        new_const(1),
                                        new_op(OP_POW,
                                               dup_expr(expr->specfunc.operand),
                                               new_const(2))),
                                 new_const(-.5))));
        case FN_COT:
            return simp_and_free(new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 diff(expr->specfunc.operand, var),
                                 new_op(OP_POW,
                                        new_specfunc(FN_CSC, dup_expr(expr->specfunc.operand)),
                                        new_const(2)))));
        case FN_ASIN:
            return simp_and_free(new_op(OP_MUL,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_POW,
                                 new_op(OP_SUB,
                                        new_const(1),
                                        new_op(OP_POW,
                                        dup_expr(expr->specfunc.operand),
                                               new_const(2))),
                                 new_const(-.5))));
        case FN_ACOS:
            return simp_and_free(new_op(OP_MUL,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_MUL,
                                 new_const(-1),
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_const(1),
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2))),
                                        new_const(-.5)))));
        case FN_ATAN:
            return simp_and_free(new_op(OP_DIV,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_ADD,
                                 new_const(1),
                                 new_op(OP_POW,
                                        dup_expr(expr->specfunc.operand),
                                        new_const(2)))));
        case FN_ACSC:
            return simp_and_free(new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 diff(expr->specfunc.operand, var),
                                 new_op(OP_DIV,
                                        new_op(OP_POW,
                                               new_op(OP_SUB,
                                                      new_op(OP_POW,
                                                             dup_expr(expr->specfunc.operand),
                                                             new_const(2)),
                                                      new_const(1)),
                                               new_const(-.5)),
                                        new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand))))));
        case FN_ASEC:
            return simp_and_free(new_op(OP_MUL,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_DIV,
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2)),
                                               new_const(1)),
                                        new_const(-.5)),
                                 new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand)))));
        case FN_ACOT:
            return simp_and_free(new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_DIV,
                                 diff(expr->specfunc.operand, var),
                                 new_op(OP_ADD,
                                        new_const(1),
                                        new_op(OP_POW,
                                               dup_expr(expr->specfunc.operand),
                                               new_const(2))))));
        case FN_ABS:
            return simp_and_free(new_op(OP_MUL,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_DIV,
                                 new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand)),
                                 dup_expr(expr->specfunc.operand))));
        case FN_NEGATE:
            return simp_and_free(new_specfunc(FN_NEGATE, diff(expr->specfunc.operand, var)));
        case FN_SQRT:
            return simp_and_free(new_op(OP_DIV,
                          diff(expr->specfunc.operand, var),
                          new_op(OP_MUL,
                                 new_const(2),
                                 new_specfunc(FN_SQRT,
                                              dup_expr(expr->specfunc.operand)))));
        default:
            fatal("fall through");
        }
    default:
        fatal("fall through");
    }
}

const char *op2s(int op)
{
    return op_names[op];
}

const char *fn2s(int fn)
{
    return fn_names[fn];
}

int s2fn(const char *tok)
{
    for(int i = 0; i < FN_LAST; ++i)
        if(!strcmp(tok, fn_names[i]))
            return i;
    return -1;
}

int s2op(const char *tok)
{
    for(int i = 0; i < OP_LAST; ++i)
        if(!strcmp(tok, op_names[i]))
            return i;
    return -1;
}

void print_expr(struct expression *expr)
{
    switch(expr->type)
    {
    case T_CONST:
        printf("%.12g ", expr->constant);
        break;
    case T_VAR:
        printf("%s ", expr->varname);
        break;
    case T_SUBEXPR:
    {
        int prec = expr_prec(*expr);
        int lprec = expr_prec(*expr->subexpr.left);
        int rprec = expr_prec(*expr->subexpr.right);

        if(lprec <= prec)
            printf("( ");
        print_expr(expr->subexpr.left);
        if(lprec <= prec)
            printf(") ");

        printf("%s ", op2s(expr->subexpr.op));

        if(rprec <= prec)
            printf("( ");
        print_expr(expr->subexpr.right);
        if(rprec <= prec)
            printf(") ");
        break;
    }
    case T_SPECFUNC:
        if(expr->specfunc.fn != FN_NEGATE)
            printf("%s( ", fn2s(expr->specfunc.fn));
        else
            printf("-");

        print_expr(expr->specfunc.operand);

        if(expr->specfunc.fn != FN_NEGATE)
            printf(") ");
        break;
    default:
        fatal("fall through");
    }
}

#define PARSER_STACK 32

#define PUSH(stack, sp, rvalue) (stack)[(sp)++] = (rvalue)
#define POP(stack, sp) ((stack)[--(sp)])

struct expression *stack_pop(struct expression **stack, int *sp)
{
    if(!*sp)
        return NULL;
    return stack[--(*sp)];
}

bool stack_push(struct expression **stack, int *sp, struct expression *value)
{
    if(*sp >= PARSER_STACK)
        return false;
    stack[(*sp)++] = value;
    return true;
}

void free_stack(struct expression **stack, int n)
{
    for(int i = 0; i < n; ++i)
        free_expr(stack[n]);
    free(stack);
}

void free_stacks(struct expression **opstack, int osp, struct expression **numstack, int nsp)
{
    free_stack(opstack, osp);
    free_stack(numstack, nsp);
}

bool is_num(const char *str)
{
    bool had_digit = false;

    if(*str == '-')
        ++str;

    while(*str)
    {
        if(!(isdigit(*str) || *str == '.'))
            return false;
        if(isdigit(*str))
            had_digit = true;
        str++;
    }
    return had_digit;
}

bool execop(struct expression **numstack, int *nsp, struct expression **opstack, int *osp)
{
    struct expression *prevop = stack_pop(opstack, osp);
    if(!prevop)
        goto fail;

    switch(prevop->type)
    {
    case T_SUBEXPR:
    {
        struct expression *r = stack_pop(numstack, nsp);
        if(!r)
            goto fail;

        struct expression *l = stack_pop(numstack, nsp);
        if(!l)
            goto fail;

        prevop->subexpr.left = l;
        prevop->subexpr.right = r;

        /* must succeed */
        stack_push(numstack, nsp, prevop);
        break;
    }
    case T_SPECFUNC:
    {
        struct expression *operand = stack_pop(numstack, nsp);
        if(!operand)
            goto fail;
        prevop->specfunc.operand = operand;
        stack_push(numstack, nsp, prevop);
        break;
    }
    default:
        fatal("fall through");
    }
    return true;
fail:
    free_expr(prevop);
    free_stacks(opstack, *osp, numstack, *nsp);
    return false;
}

struct expression *parse_expr(const char *infix)
{
    /* strtok modifies */
    char *str = strdup(infix);

    struct expression **numstack = calloc(PARSER_STACK, sizeof(struct expression*));
    int nsp = 0;

    struct expression **opstack = calloc(PARSER_STACK, sizeof(struct expression*));
    int osp = 0;

    char *tok, *p = str;
    do {
        /* tokenize */
        tok = strtok(p, " ");
        p = NULL;

        if(!tok)
            break;
        if(is_num(tok))
        {
            /* number */
            struct expression *n = new_const(atof(tok));
            if(!stack_push(numstack, &nsp, n))
            {
                free_stacks(opstack, osp, numstack, nsp);
                free_expr(n);
                free(str);
                return NULL;
            }
        }
        /* must come before operators, since unary minus is implemented as a function */
        else if(s2fn(tok) >= 0 && (s2fn(tok) != FN_NEGATE || (s2fn(tok) == FN_NEGATE && nsp == 0)))
        {
            struct expression *n = new_specfunc(s2fn(tok), NULL);
            if(!stack_push(opstack, &osp, n))
            {
                free_stacks(opstack, osp, numstack, nsp);
                free_expr(n);
                free(str);
                return NULL;
            }
        }
        else if(s2op(tok) >= 0)
        {
            struct expression *op = new_op(s2op(tok), NULL, NULL);
            while(osp > 0 && (opstack[osp-1]->type == T_SPECFUNC ||
                              (expr_prec(*opstack[osp-1]) > expr_prec(*op)) ||
                              (expr_prec(*opstack[osp-1]) == expr_prec(*op) && op_assoc[(int)opstack[osp-1]->subexpr.op] == LEFT)))
            {
                if(!execop(numstack, &nsp, opstack, &osp))
                {
                    free_expr(op);
                    free(str);
                    return NULL;
                }
            }

            if(!stack_push(opstack, &osp, op))
            {
                free_stacks(opstack, osp, numstack, nsp);
                free_expr(op);
                free(str);
                return NULL;
            }
        }
        else if(!strcmp(tok, "("))
        {
            struct expression *op = new_op(OP_LPAREN, NULL, NULL);
            if(!stack_push(opstack, &osp, op))
            {
                free_stacks(opstack, osp, numstack, nsp);
                free_expr(op);
                free(str);
                return NULL;
            }
        }
        else if(!strcmp(tok, ")"))
        {
            while(osp > 0 && opstack[osp - 1]->subexpr.op != OP_LPAREN)
            {
               if(!execop(numstack, &nsp, opstack, &osp))
               {
                   free(str);
                   return NULL;
               }
            }
            free_expr(stack_pop(opstack, &osp));
        }
        else
        {
            /* variable name */
            struct expression *var = new_var(tok);
            if(!stack_push(numstack, &nsp, var))
            {
                free_stacks(opstack, osp, numstack, nsp);
                free_expr(var);
                free(str);
                return NULL;
            }
        }
    } while(tok);

    while(osp > 0)
    {
        if(!execop(numstack, &nsp, opstack, &osp))
        {
            free(str);
            return NULL;
        }
    }

    free(str);

    struct expression *ret = numstack[0];

    /* guaranteed to be empty */
    free(opstack);

    if(nsp != 1)
    {
        /* we free the memory for the stack, as well as the elements,
         * since we don't care about them */
        free_stack(numstack, nsp);
        return NULL;
    }
    else
    {
        /* only free the stack memory, leaving the element untouched */
        free(numstack);
        return ret;
    }
}

int main(int argc, char *argv[])
{
    interactive = isatty(STDIN_FILENO);

    if(interactive)
    {
        printf("Welcome to yaCAS!\n\nCopyright (C) 2018 Franklin Wei\n\nType \"help\" for a quick overview of the supported features.\n*** Remember to separate tokens with spaces ***\n\n");
    }

    atexit(freevars);

    setvar("pi", new_const(M_PI), true);
    setvar("e", new_const(M_E), true);
    setvar("memdiag", new_const(0), false);
    setvar(".", new_const(0), false);

    while(1)
    {
        if(setjmp(restore) == 0)
        {
            peakmem = 0;

            char *line = NULL;
#ifndef USE_READLINE
            if(interactive)
                printf("yaCAS> ");
            fflush(stdout);

            size_t n = 0;
            ssize_t len = getline(&line, &n, stdin);

            /* remove newline */
            if(line[len - 1] == '\n')
                line[len-- - 1] = '\0';

            if(len < 0)
                return 0;
#else
            line = readline(interactive ? "yaCAS> " : "");
            if(line && *line)
                add_history(line);
#endif

            if(!line)
                return 0;

            if(!strcmp(line, "dump"))
            {
                dumpvars();
                free(line);
                continue;
            }
            else if(!strcmp(line, "help"))
            {
                printf("yaCAS requires a space between all tokens, so instead of \"x^2\", type \"x ^ 2\"\n");
                printf("Some features in action:\n");

                printf("Calculation:\n    > atan ( 1 ) / pi\n");
                printf("Differentiation:\n    > x ^ 2 diff ( x = 2 ) -- differentiate x^2 at x=2\n    > log ( y ) * x diff x -- implicit differentiation\n    > exp ( x ^ 2 ) diff x diff ( x = 0 ) -- evaluate higher-order derivative\n");
                printf("Integration (rudimentary):\n    > 5 * x ^ 3 int x\n");
                printf("Special functions:\n    > exp ( pi ) - pi\n");
                printf("Variables:\n    > y = x ^ 2 -- variables can contain other expressions\n    > y diff x -- differentiate x^2 with respect to x\n    > x = 2\n    > y\n");
                printf("Equality testing (rudimentary):\n    > x + 2 == 2 + x\n");
                free(line);
                continue;
            }

            clock_t start = clock();

            struct expression *top = parse_expr(line);
            free(line);

            if(top)
            {
                top = eval_and_free(top);
                top = simp_and_free_max(top);
                print_expr(top);

                printf("(%s)\n", type_names[(int)top->type]);

                setvar(".", dup_expr(top), true);

                free_expr(top);
            }
            else
            {
                printf("malformed expression\n");
            }

            clock_t diff = clock() - start;
            if(diff > CLOCKS_PER_SEC / 10)
                printf("time: %ld.%.03ld sec\n", diff / CLOCKS_PER_SEC, diff % CLOCKS_PER_SEC / (CLOCKS_PER_SEC / 1000));

            if(eval_numexpr_and_free(new_var("memdiag")) == 2)
            {
                printf("memory: %d peak: %d\n", memusage, peakmem);
            }
        }
    }
}
