#define USE_READLINE

#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifdef USE_READLINE
#include <readline/readline.h>
#include <readline/history.h>
#endif

/* tool for manipulating algebraic expressions */
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
};

enum { OP_POW = 0, OP_MUL, OP_DIV, OP_ADD, OP_SUB, OP_DIFF, OP_ASSIGN, OP_EQUALS, OP_LAST, /* not a real operator: */ OP_LPAREN };
enum { T_CONST = 0, T_VAR, T_SUBEXPR, T_SPECFUNC };
enum { FN_LOG = 0, FN_EXP, FN_SIN, FN_COS, FN_TAN, FN_CSC, FN_SEC, FN_COT, FN_ASIN, FN_ACOS, FN_ATAN, FN_ACSC, FN_ASEC, FN_ACOT, FN_ABS, FN_NEGATE, FN_SQRT, FN_LAST };
enum { RIGHT, LEFT };

const char *op_names[] = {
    "^", "*", "/", "+", "-", "diff", "=", "=="
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
double eval_numexpr(struct expression *expr);
struct expression *diff(struct expression *expr, const char *var);
struct expression *dup_expr(struct expression *expr);
struct expression *eval_expr(struct expression *expr);
struct expression *simp(struct expression *expr);
void print_expr(struct expression *expr);
void setvar(const char *name, struct expression *value, bool constant);

bool simp_progress = false;
bool memdiag = false;

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
    if(memdiag)
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
    if(memdiag)
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
    if(memdiag)
        printf("new op %p\n", new);
    return new;
}

struct expression *new_specfunc(int fn, struct expression *expr)
{
    struct expression *new = calloc(1, sizeof(*new));
    new->type = T_SPECFUNC;
    new->specfunc.fn = fn;
    new->specfunc.operand = expr;
    memusage += sizeof(*new);
    if(memdiag)
        printf("new specfunc %p\n", new);
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
        if(memdiag)
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
    if(l == r)
        return true;

    /* duplicate them first so we can modify them if need be */
    l = dup_expr(l);
    r = dup_expr(r);

    l = simp_and_free_max(l);
    r = simp_and_free_max(r);

    if(is_constant(l) && is_constant(r))
        return eval_numexpr(l) == eval_numexpr(r);

    /* not foolproof */
    if(l->type != r->type)
        return false;

    switch(l->type)
    {
    case T_SUBEXPR:
        /* todo */
        return false;
    case T_SPECFUNC:
        return l->specfunc.fn == r->specfunc.fn && expr_equals(l->specfunc.operand, r->specfunc.operand);
    case T_VAR:
        /* symbolic comparison */
        if(!is_var(l->varname) && !is_var(r->varname))
            return !strcmp(l->varname, r->varname);
        break;
    default:
        break;
    }

    /* try evaluating them and recurse */
    l = eval_and_free(l);
    r = eval_and_free(r);
    return expr_equals(l, r);
}

#define VARMAP_SIZE 10

/* chained hash map */
struct variable {
    const char *name;
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

/* value must be persistent */
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
            printf("(%s)\n", type_names[i->value->type]);
            i = i->next;
        }
    }
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
        if(rexpr->type != T_VAR)
            fatal("diff operator must take variable as second operand");
        return diff(eval_expr(lexpr), rexpr->varname);
    }
    else if(op == OP_ASSIGN)
    {
        if(lexpr->type != T_VAR)
            fatal("assignment requires variable as first operand");
        if(is_constvar(lexpr->varname))
            fatal("cannot change constant value");
        if(expr_references(rexpr, lexpr->varname))
            fatal("circular reference");

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
            fatal("fall through");
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
        fatal("fall through");
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
        fatal("attempted to numerically evaluate non-numeric expression");
    }
    free_expr(result);
    return x;
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
            if(expr->subexpr.left->type == T_SUBEXPR && expr->subexpr.left->subexpr.op == OP_POW && is_constant(expr->subexpr.left->subexpr.right) && is_constant(expr->subexpr.right))
            {
                simp_progress = true;
                return new_op(OP_POW, simp(expr->subexpr.left->subexpr.left), new_const(eval_numexpr(expr->subexpr.left->subexpr.right) * eval_numexpr(expr->subexpr.right)));
            }
            return new_op(expr->subexpr.op, simp(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_DIFF:
            assert(expr->subexpr.right->type == T_VAR);
            return new_op(OP_DIFF, simp(expr->subexpr.left), dup_expr(expr->subexpr.right));
        case OP_ASSIGN:
            return new_op(OP_ASSIGN, dup_expr(expr->subexpr.left), simp(expr->subexpr.right));
        case OP_EQUALS:
            return new_op(OP_EQUALS, dup_expr(expr->subexpr.left), dup_expr(expr->subexpr.right));
        default:
            fatal("fall through");
        }
        break;
    case T_SPECFUNC:
        return new_specfunc(expr->specfunc.fn, simp(expr->specfunc.operand));
    default:
        fatal("fall through");
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
            if(is_var(expr->varname))
                return diff(eval_expr(expr), var);
            //if(is_constant(expr))
            //return new_const(0);
            return new_op(OP_DIFF, dup_expr(expr), new_var(var));
        }
    case T_SUBEXPR:
        switch(expr->subexpr.op)
        {
        case OP_ADD:
        case OP_SUB:
            return new_op(expr->subexpr.op, simp_and_free(diff(expr->subexpr.left, var)), simp_and_free(diff(expr->subexpr.right, var)));
        case OP_MUL:
            /* f'g + fg' */
            return new_op(OP_ADD,
                          simp_and_free(new_op(OP_MUL, simp_and_free(diff(expr->subexpr.left, var)), dup_expr(expr->subexpr.right))),
                          simp_and_free(new_op(OP_MUL, dup_expr(expr->subexpr.left), simp_and_free(diff(expr->subexpr.right, var)))));
        case OP_DIV:
            return new_op(OP_DIV,
                          new_op(OP_SUB,
                                 new_op(OP_MUL, simp_and_free(diff(expr->subexpr.left, var)), dup_expr(expr->subexpr.right)),
                                 new_op(OP_MUL, dup_expr(expr->subexpr.left), simp_and_free(diff(expr->subexpr.right, var)))),
                          new_op(OP_POW, dup_expr(expr->subexpr.right), new_const(2)));
        case OP_POW:
            /* just n * f(x) ^ (n - 1) * f'(x) */
#if 0
            if(is_constant(expr->subexpr.right))
            {
                return new_op(OP_MUL,
                              new_const(eval_numexpr(expr->subexpr.right)),
                              new_op(OP_MUL,
                                     simp_and_free(new_op(OP_POW,
                                                          dup_expr(expr->subexpr.left),
                                                          new_op(OP_SUB,
                                                                 dup_expr(expr->subexpr.right),
                                                                 new_const(1)))),
                                     simp_and_free(diff(expr->subexpr.left, var))));
            }
            else
#endif
            {
                /* f^(g-1) * (gf' + fg'ln(f)) */
                return new_op(OP_MUL,
                              new_op(OP_POW,
                                     dup_expr(expr->subexpr.left),
                                     new_op(OP_SUB,
                                            dup_expr(expr->subexpr.right),
                                            new_const(1))),
                              new_op(OP_ADD,
                                     new_op(OP_MUL,
                                            dup_expr(expr->subexpr.right),
                                            simp_and_free(diff(expr->subexpr.left, var))),
                                     new_op(OP_MUL,
                                            dup_expr(expr->subexpr.left),
                                            new_op(OP_MUL,
                                                   simp_and_free(diff(expr->subexpr.right, var)),
                                                   new_specfunc(FN_LOG, dup_expr(expr->subexpr.left))))));
            }
        case OP_DIFF:
            return diff_and_free(diff(expr->subexpr.left, expr->subexpr.right->varname), var);
        case OP_ASSIGN:
            /* todo: how to make this logical? */
            break;
        case OP_EQUALS:
            /* todo: how to make this logical? */
            break;
        default:
            fatal("fall through");
        }
    case T_SPECFUNC:
        switch(expr->specfunc.fn)
        {
        case FN_LOG:
            return new_op(OP_DIV,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          dup_expr(expr->specfunc.operand));
        case FN_EXP:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_specfunc(FN_EXP, dup_expr(expr->specfunc.operand)));
        case FN_SIN:
            return new_op(OP_MUL,
                          new_specfunc(FN_COS, dup_expr(expr->specfunc.operand)),
                          simp_and_free(diff(expr->specfunc.operand, var)));
        case FN_COS:
            return new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 new_specfunc(FN_SIN, dup_expr(expr->specfunc.operand)),
                                 simp_and_free(diff(expr->specfunc.operand, var))));
        case FN_TAN:
            return new_op(OP_DIV,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_POW,
                                 new_specfunc(FN_COS,
                                              dup_expr(expr->specfunc.operand)),
                                 new_const(2)));
        case FN_CSC:
            return new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 simp_and_free(diff(expr->specfunc.operand, var)),
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_const(1),
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2))),
                                        new_const(-.5))));
        case FN_SEC:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_POW,
                                 new_op(OP_SUB,
                                        new_const(1),
                                        new_op(OP_POW,
                                               dup_expr(expr->specfunc.operand),
                                               new_const(2))),
                                 new_const(-.5)));
        case FN_COT:
            return new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 simp_and_free(diff(expr->specfunc.operand, var)),
                                 new_op(OP_POW,
                                        new_specfunc(FN_CSC, dup_expr(expr->specfunc.operand)),
                                        new_const(2))));
        case FN_ASIN:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_POW,
                                 new_op(OP_SUB,
                                        new_const(1),
                                        new_op(OP_POW,
                                        dup_expr(expr->specfunc.operand),
                                               new_const(2))),
                                 new_const(-.5)));
        case FN_ACOS:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_MUL,
                                 new_const(-1),
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_const(1),
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2))),
                                        new_const(-.5))));
        case FN_ATAN:
            return new_op(OP_DIV,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_ADD,
                                 new_const(1),
                                 new_op(OP_POW,
                                        dup_expr(expr->specfunc.operand),
                                        new_const(2))));
        case FN_ACSC:
            return new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_MUL,
                                 simp_and_free(diff(expr->specfunc.operand, var)),
                                 new_op(OP_DIV,
                                        new_op(OP_POW,
                                               new_op(OP_SUB,
                                                      new_op(OP_POW,
                                                             dup_expr(expr->specfunc.operand),
                                                             new_const(2)),
                                                      new_const(1)),
                                               new_const(-.5)),
                                        new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand)))));
        case FN_ASEC:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_DIV,
                                 new_op(OP_POW,
                                        new_op(OP_SUB,
                                               new_op(OP_POW,
                                                      dup_expr(expr->specfunc.operand),
                                                      new_const(2)),
                                               new_const(1)),
                                        new_const(-.5)),
                                 new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand))));
        case FN_ACOT:
            return new_op(OP_MUL,
                          new_const(-1),
                          new_op(OP_DIV,
                                 simp_and_free(diff(expr->specfunc.operand, var)),
                                 new_op(OP_ADD,
                                        new_const(1),
                                        new_op(OP_POW,
                                               dup_expr(expr->specfunc.operand),
                                               new_const(2)))));
        case FN_ABS:
            return new_op(OP_MUL,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_DIV,
                                 new_specfunc(FN_ABS, dup_expr(expr->specfunc.operand)),
                                 dup_expr(expr->specfunc.operand)));
        case FN_NEGATE:
            return new_specfunc(FN_NEGATE, simp_and_free(diff(expr->specfunc.operand, var)));
        case FN_SQRT:
            return new_op(OP_DIV,
                          simp_and_free(diff(expr->specfunc.operand, var)),
                          new_op(OP_MUL,
                                 new_const(2),
                                 new_specfunc(FN_SQRT,
                                              dup_expr(expr->specfunc.operand))));
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
                              (expr_prec(*opstack[osp-1]) == expr_prec(*op) && op_assoc[opstack[osp-1]->subexpr.op] == LEFT)))
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
    setvar("pi", new_const(M_PI), true);
    setvar("e", new_const(M_E), true);
    while(1)
    {
        peakmem = 0;

        char *line = NULL;
#ifndef USE_READLINE
        printf("yaCAS> ");
        fflush(stdout)

        size_t n = 0;
        size_t len = getline(&line, &n, stdin);

        /* remove newline */
        if(line[len - 1] == '\n')
            line[len-- - 1] = '\0';
#else
        line = readline("yaCAS> ");
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

        struct expression *top = parse_expr(line);
        free(line);

        if(top)
        {
            top = eval_and_free(top);
            top = simp_and_free_max(top);
            print_expr(top);
            printf("(%s)\n", type_names[top->type]);

            setvar(".", dup_expr(top), true);

            free_expr(top);
        }
        else
            printf("malformed expression\n");

        if(memdiag)
            printf("memory: %d peak: %d\n", memusage, peakmem);
    }
}
