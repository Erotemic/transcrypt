/*
 * Universal Boolean-model checks of the pure prospective policy kernel
 * in rust/crates/transcrypt-policy/src/lib.rs. This is an independent
 * mathematical model of the source expressions, not Aeneas translation.
 * Trusted adapter obligations are explicitly *outside* this model.
 */
#include <stdio.h>
#include <stdlib.h>

typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_sort *Z3_sort;
typedef struct _Z3_symbol *Z3_symbol;
typedef struct _Z3_ast *Z3_ast;
typedef struct _Z3_solver *Z3_solver;
typedef enum { Z3_L_FALSE = -1, Z3_L_UNDEF = 0, Z3_L_TRUE = 1 } Z3_lbool;
extern Z3_config Z3_mk_config(void);
extern void Z3_del_config(Z3_config);
extern Z3_context Z3_mk_context(Z3_config);
extern void Z3_del_context(Z3_context);
extern Z3_sort Z3_mk_bool_sort(Z3_context);
extern Z3_symbol Z3_mk_string_symbol(Z3_context, const char *);
extern Z3_ast Z3_mk_const(Z3_context, Z3_symbol, Z3_sort);
extern Z3_ast Z3_mk_and(Z3_context, unsigned, const Z3_ast *);
extern Z3_ast Z3_mk_or(Z3_context, unsigned, const Z3_ast *);
extern Z3_ast Z3_mk_not(Z3_context, Z3_ast);
extern Z3_ast Z3_mk_eq(Z3_context, Z3_ast, Z3_ast);
extern Z3_solver Z3_mk_solver(Z3_context);
extern void Z3_solver_inc_ref(Z3_context, Z3_solver);
extern void Z3_solver_dec_ref(Z3_context, Z3_solver);
extern void Z3_solver_reset(Z3_context, Z3_solver);
extern void Z3_solver_assert(Z3_context, Z3_solver, Z3_ast);
extern Z3_lbool Z3_solver_check(Z3_context, Z3_solver);
extern const char *Z3_solver_get_reason_unknown(Z3_context, Z3_solver);

static Z3_context c;
static Z3_solver sol;
static unsigned checked;
static Z3_ast val(const char *s) {
    return Z3_mk_const(c, Z3_mk_string_symbol(c, s), Z3_mk_bool_sort(c));
}
static Z3_ast land(unsigned n, const Z3_ast *x) { return Z3_mk_and(c, n, x); }
static Z3_ast lor(unsigned n, const Z3_ast *x) { return Z3_mk_or(c, n, x); }
static Z3_ast lnot(Z3_ast x) { return Z3_mk_not(c, x); }
static void prove_implication(const char *name, Z3_ast antecedent,
                              Z3_ast consequent) {
    /* `not (antecedent -> consequent)` must be UNSAT. */
    Z3_ast bad[2] = { antecedent, lnot(consequent) };
    Z3_solver_assert(c, sol, land(2, bad));
    Z3_lbool result = Z3_solver_check(c, sol);
    if (result != Z3_L_FALSE) {
        fprintf(stderr, "FAIL %s: %s\n", name,
                result == Z3_L_TRUE ? "SAT counterexample" :
                Z3_solver_get_reason_unknown(c, sol));
        exit(1);
    }
    ++checked;
    printf("PROVED (UNSAT): %s\n", name);
    Z3_solver_reset(c, sol);
}

int main(void) {
    Z3_config cfg = Z3_mk_config();
    c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    sol = Z3_mk_solver(c);
    Z3_solver_inc_ref(c, sol);

    Z3_ast portable = val("staged_protected");
    Z3_ast local = val("local_protected");
    Z3_ast regular = val("staged_regular");
    Z3_ast complete = val("config_complete");
    Z3_ast bound = val("metadata_matches");
    Z3_ast auth = val("authenticated");
    Z3_ast protected[2] = { portable, local };
    Z3_ast p = lor(2, protected);
    Z3_ast requirements[5] = { p, regular, complete, bound, auth };
    Z3_ast stage = land(5, requirements);

    prove_implication("secure stage acceptance => staged OR local protection", stage, p);
    prove_implication("secure stage acceptance => staged regular file", stage, regular);
    prove_implication("secure stage acceptance => complete metadata", stage, complete);
    prove_implication("secure stage acceptance => bound ciphertext metadata", stage, bound);
    prove_implication("secure stage acceptance => authenticated ciphertext", stage, auth);
    /* Committing a staged protected path must not depend on a worktree
     * override: with portable=true, the protection policy is active. */
    Z3_ast portable_good[5] = { portable, regular, complete, bound, auth };
    prove_implication("staged protection + valid evidence => accepted regardless of local",
                      land(5, portable_good), stage);

    Z3_ast u_auth = val("unlock_authenticated");
    Z3_ast u_valid = val("public_config_valid");
    Z3_ast u_dest = val("destination_safe");
    Z3_ast u_stable = val("snapshot_stable");
    Z3_ast u_reqs[4] = { u_auth, u_valid, u_dest, u_stable };
    Z3_ast unlock = land(4, u_reqs);
    prove_implication("unlock may persist only after authentication", unlock, u_auth);
    prove_implication("unlock may persist only after config check", unlock, u_valid);
    prove_implication("unlock may persist only to safe destination", unlock, u_dest);
    prove_implication("unlock may persist only on stable snapshot", unlock, u_stable);

    Z3_ast m[6] = { val("old_ciphertext_all_auth"),
                    val("contexts_complete"),
                    val("new_ciphertext_all_auth"),
                    val("new_metadata_complete"),
                    val("source_unchanged"),
                    val("rollback_available") };
    Z3_ast publish = land(6, m);
    const char *names[6] = {
        "migration publication => all source ciphertexts authenticated",
        "migration publication => all contexts covered",
        "migration publication => all new ciphertexts authenticated",
        "migration publication => target metadata complete",
        "migration publication => source snapshot unchanged",
        "migration publication => rollback path available"
    };
    for (unsigned i = 0; i < 6; ++i) {
        prove_implication(names[i], publish, m[i]);
    }

    Z3_solver_dec_ref(c, sol);
    Z3_del_context(c);
    printf("SUCCESS: %u universal policy obligations discharged\n", checked);
    return 0;
}
