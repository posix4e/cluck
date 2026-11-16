/*
Natural numbers that fit in a machine word.

Compiled Lean does small-number arithmetic inline and comes here only when a number is, or might become,
too large for that. The operations below are the ones it calls for every operand, small or not. Their
small cases are answered here; an operand or a result that is not small goes to the big-number code (big.c).

A small natural number is below 2^63 and travels as a tagged word, not a pointer.
*/
#include "big.h"

/* A Nat used as a size. Lean's runtime gives the value when it fits a word and reports "out of memory"
when it does not, since no array is that large. Lean's runtime also takes over the caller's reference to a
number that is not small; this borrows, so a caller that owns such a number still has to release it. */
size_t rt_nat_to_size(b_lean_obj_arg nat) {
    if (lean_is_scalar(nat)) return lean_unbox(nat);
    return rt_big_nat_to_size(nat);
}

/* `a <<< b`. */
lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (lean_is_scalar(a1) && lean_unbox(a1) == 0) return lean_box(0);
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) lean_internal_panic("Nat.shiftl exponent is too big");
    if (lean_is_scalar(a1)) {
        size_t value = lean_unbox(a1);
        size_t shift = lean_unbox(a2);
        if (shift < 63 && (value >> (63 - shift)) == 0) return lean_box(value << shift);
    }
    return rt_big_nat_shiftl(a1, lean_unbox(a2));
}

/* `a ^ b`. */
lean_obj_res lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
        if (lean_is_scalar(a1)) {
            if (lean_unbox(a1) == 0) return lean_box(0);
            if (lean_unbox(a1) == 1) return lean_box(1);
        }
        lean_internal_panic("Nat.pow exponent is too big");
    }
    if (lean_is_scalar(a1)) {
        size_t base = lean_unbox(a1);
        size_t exponent = lean_unbox(a2);
        size_t result = 1;
        bool fits = true;
        /* Square and multiply, stopping as soon as anything leaves the small range. */
        while (exponent != 0 && fits) {
            if (exponent & 1) {
                fits = !__builtin_mul_overflow(result, base, &result) && result <= LEAN_MAX_SMALL_NAT;
            }
            exponent >>= 1;
            if (exponent != 0 && fits) {
                fits = !__builtin_mul_overflow(base, base, &base) && base <= LEAN_MAX_SMALL_NAT;
            }
        }
        if (fits) return lean_box(result);
    }
    return rt_big_nat_pow(a1, lean_unbox(a2));
}

/* The position of the highest set bit; 0 for 0 and 1. */
lean_obj_res lean_nat_log2(b_lean_obj_arg a) {
    if (lean_is_scalar(a)) {
        size_t value = lean_unbox(a);
        unsigned result = 0;
        while (value >= 2) {
            result++;
            value /= 2;
        }
        return lean_box(result);
    }
    return lean_box(rt_big_nat_log2(a));
}
