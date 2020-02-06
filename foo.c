#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#define MAXINTLEN 10 // 80 bit should be enough

struct _subexpr_t;
typedef struct _subexpr_t subexpr_t;

typedef void (*evalfun_t)(subexpr_t *restrict, const uint8_t *restrict);

struct _subexpr_t {
    uint8_t res[1 + MAXINTLEN];
    evalfun_t fun;
    union {
        struct {
            subexpr_t *left, *right;    
        } node;
        struct {
            subexpr_t *fun;
            size_t num_args;
            subexpr_t *args;
        } call;
        size_t var;
        uint8_t con[MAXINTLEN + 1];
    } detail;
};

typedef struct {
    size_t args;
    subexpr_t *calc;
} equation_t;

void eval_const(subexpr_t *restrict exp, __attribute__((unused)) const uint8_t *restrict vars) {
    memcpy(exp->res, exp->detail.con, exp->detail.con[0] + 1);
}

void eval_var(subexpr_t *restrict exp, const uint8_t *restrict vars) {
    const uint8_t *var = vars + (1 + MAXINTLEN) * exp->detail.var;
    memcpy(exp->res, var, var[0] + 1);
}

void eval_call(subexpr_t *restrict exp, const uint8_t *restrict vars) {
    uint8_t *args = (uint8_t*) alloca(exp->detail.call.num_args * (1 + MAXINTLEN));
    for (size_t i = 0; i < exp->detail.call.num_args; ++i) {
        subexpr_t *cur = &exp->detail.call.args[i];
        cur->fun(cur, vars);
        memcpy(args + (1 + MAXINTLEN) * i, cur->res, cur->res[0] + 1);
    }
    exp->detail.call.fun->fun(exp->detail.call.fun, args);
    memcpy(exp->res, exp->detail.call.fun->res, exp->detail.call.fun->res[0] + 1);
}

void eval_mul(subexpr_t *restrict exp, const uint8_t *restrict vars) {
    exp->detail.node.left->fun(exp->detail.node.left, vars);
    exp->detail.node.right->fun(exp->detail.node.right, vars);
    uint8_t *le = exp->detail.node.left->res;
    uint8_t *ri = exp->detail.node.right->res;
    memset(exp->res, 0, le[0] + ri[0] + 1);
    uint8_t maxl = 1;
    
    for (uint8_t i = 0; i < le[0]; ++i) {
        uint16_t carry = 0;
        uint8_t j;
        for (j = 0; j < ri[0]; ++j) {
            carry += exp->res[1 + i + j] + (uint16_t) le[1 + i] * ri[1 + j];
            exp->res[1 + i + j] = carry;
            carry >>= 8;
        }
        for (;carry;++j) {
            carry += exp->res[1 + i + j];
            exp->res[1 + i + j] = carry;
            carry >>= 8;
        }
        if (i + j > maxl)
            maxl = i + j;
    }
    exp->res[0] = maxl;
}

void win() {
    system("get_flag");
    exit(0);
}

# evtl auch nicht 32 bit
# s.send(struct.pack("<Q", 0x400c20))
# 0x400c20 <win>:	0xe5894855
# 0x400c20 <win>:	0xe5894855

void eval_add(subexpr_t *restrict exp, const uint8_t *restrict vars) {
    uint8_t minl, maxl;
    uint8_t *longer;
    exp->detail.node.left->fun(exp->detail.node.left, vars);
    exp->detail.node.right->fun(exp->detail.node.right, vars);
    uint8_t *le = exp->detail.node.left->res;
    uint8_t *ri = exp->detail.node.right->res;

    if (le[0] < ri[0]) {
        minl = le[0];
        maxl = ri[0];
        longer = ri;
    } else {
        minl = ri[0];
        maxl = le[0];
        longer = le;
    }
    
    uint16_t carry = 0;
    uint8_t idx;
    for (idx = 1; idx <= minl; ++idx) {
        carry += le[idx] + ri[idx];
        exp->res[idx] = (uint8_t) carry;
        carry >>= 8;
    }
    for (; idx <= maxl; ++idx) {
        carry += longer[idx];
        exp->res[idx] = (uint8_t) carry;
        carry >>= 8;
    }
    if (carry) {
        exp->res[idx] = 1;
        idx++;
    }
    exp->res[0] = idx - 1;
}

void print_val(uint8_t *val) {
    printf("%hhx", val[val[0]]);
    for (uint8_t i = val[0] - 1; i > 0; --i)
        printf("%02hhx", val[i]);
}

void whitespace(char **txt) {
    while (**txt == ' ' || **txt == '\t') {
        ++*txt;
    }
}

equation_t bound[27] = {};

#define ASSERT(cnd, err)    \
if (!(cnd)) {               \
    puts(err);              \
    return NULL;            \
}

subexpr_t *parse_exp(char **txt, const char *restrict vars) {
    whitespace(txt);
    char op = **txt;
    size_t args = 0;
    char *idx;
    subexpr_t *ret = calloc(sizeof(subexpr_t), 1);
    
    if ((unsigned) op - 0x30 <= 9) {
        char *aft = NULL;
        uint64_t val = strtoull(*txt, &aft, 10);
        ASSERT(*txt != aft, "error parsing a constant")
        *txt = aft;
        ret->fun = eval_const;
        size_t i = 0;
        do {
            ret->detail.con[++i] = val;
            val >>= 8;
        } while(val);
        ret->detail.con[0] = i;
        return ret;
    }
    
    ++*txt;
    if ((idx = strchr(vars, op))) {
        ret->fun = eval_var;
        ret->detail.var = (size_t) (idx - vars);
        return ret;
    } else if (op == '+' || op == '*') {
        args = 2;
        ret->fun = op == '+' ? eval_add : eval_mul;
        ASSERT((ret->detail.node.left = parse_exp(txt, vars)), "error parsing left expr")
        ASSERT((ret->detail.node.right = parse_exp(txt, vars)), "error parsing right expr")
        return ret;
    } else {
        size_t idx = (op | 0x20) - 0x61;
        ASSERT(idx < 26, "error: not a var")
        ASSERT(bound[idx].calc, "error: var not bound")
        ret->fun = eval_call;
        ret->detail.call.fun = bound[idx].calc;
        ret->detail.call.num_args = bound[idx].args;
        ret->detail.call.args = calloc(sizeof(subexpr_t), bound[idx].args);
        for (size_t i = 0; i < bound[idx].args; ++i) {
            subexpr_t *tmp;
            ASSERT((tmp = parse_exp(txt, vars)), "error parsing function argument")
            memcpy(&ret->detail.call.args[i], tmp, sizeof(*tmp));
        }
        return ret;
    }
    ASSERT(0, "unable to parse")
}
#undef ASSERT

size_t parse(char *txt) {
    size_t lvar = 26;
    char vars[27] = {0};
    char *tmp;
    size_t num_args = 0;
    char *cur = txt;

    if ((tmp = strchr(cur, '='))) {
        whitespace(&cur);
        char v = *cur;
        lvar = (v | 0x20) - 0x61;
        if (lvar >= 26) {
            puts("error parsing lvar");
            return 27;
        }
        cur = tmp + 1;
    }

    if ((tmp = strchr(cur, '.'))) {
        whitespace(&cur);
        while (cur < tmp) {
            char v = *cur;
            ++cur;
            vars[num_args++] = v;
            whitespace(&cur);
        }
        ++cur;
    }

    subexpr_t *exp = parse_exp(&cur, vars);
    if (exp == NULL)
        return 27;

    bound[lvar].args = num_args;
    bound[lvar].calc = exp;

    return lvar;
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    char line[1024];
    puts("Welcome to Big Math as a Service (BMaaS)");
    puts("Only positvie operations are implemented tho -- because we don't need that negativity");
    printf("> ");
    while (fgets(line, sizeof(line), stdin)) {
        size_t idx = parse(line);
        if (idx <= 26) {
            if (bound[idx].args == 0) {
                bound[idx].calc->fun(bound[idx].calc, NULL);
                print_val(bound[idx].calc->res);
                puts("");
            }
        }
        printf("> ");
    }
    return 0;
}
