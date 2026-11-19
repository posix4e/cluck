/*
Three names compiled Jaune asks its runtime for that the minimal runtime does not have. None holds any logic:
each hands over to something that is already there. `scripts/build-min` fails at the link if a fourth is
ever needed.
*/
#include <lean/lean.h>

/* Compiled Lean that imports Lean's own library starts with this and not with
   lean_initialize_runtime_module. There is no more to start here than there. */
void lean_initialize_runtime_module(void);
void lean_initialize(void) { lean_initialize_runtime_module(); }

/* The successor of a number too large for a machine word. */
lean_obj_res lean_nat_big_succ(b_lean_obj_arg a) { return lean_nat_big_add(a, lean_box(1)); }

/* Nat.powMod: Evm/PowMod.lean, which is Lean. */
lean_object * evm_nat_powmod(lean_object * b, lean_object * e, lean_object * m);
lean_obj_res lean_nat_powmod(b_lean_obj_arg b, b_lean_obj_arg e, b_lean_obj_arg m) {
    /* The caller lends its three numbers; the Lean takes its arguments for its own. */
    lean_inc(b);
    lean_inc(e);
    lean_inc(m);
    return evm_nat_powmod(b, e, m);
}
