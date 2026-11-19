/*
Start-up routines of seven mathlib modules, as routines that do nothing.

Three of Jaune's modules import mathlib for their proofs. A compiled Lean module starts by running the
start-up routine of everything it imports, so those imports would link mathlib, and behind it Lean's compiler
and its 110 or so runtime functions the minimal runtime does not have, into the image, to build constants
that the code which runs never reads. With these seven in their place none of that is linked.

This is a claim, not a proof: that no Jaune code reached by the service reads a constant one of those modules
would have built. If one did, it would read memory nothing has written. What stands behind the claim is that
the service gives the fixtures' answers linked this way (README.md). The repair is in Jaune, not here: keep
proofs out of the modules that run, which is this repository's own rule for itself.
*/
#include <lean/lean.h>

#define NOTHING(name) \
    lean_object * name(uint8_t builtin) { (void)builtin; return lean_io_result_mk_ok(lean_box(0)); }

NOTHING(initialize_mathlib_Mathlib_Data_List_Chain)
NOTHING(initialize_mathlib_Mathlib_Data_List_Lemmas)
NOTHING(initialize_mathlib_Mathlib_Data_List_TakeDrop)
NOTHING(initialize_mathlib_Mathlib_Data_List_TakeWhile)
NOTHING(initialize_mathlib_Mathlib_Data_Nat_Basic)
NOTHING(initialize_mathlib_Mathlib_Data_UInt)
NOTHING(initialize_mathlib_Mathlib_Tactic_NormNum)
