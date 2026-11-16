/*
Numbers too large for a machine word.

Compiled Lean keeps a natural number below 2^63, and an integer that fits in 32 bits, in a tagged word and
does the arithmetic on it inline. For anything else it calls the functions in this file, which replace the
part of Lean's runtime that stands on GMP.

A big number is one heap object: a sign, a count, and that many 32-bit limbs, least significant first. It
points at nothing, so object.c can free it or make it permanent without looking inside. Natural numbers and
integers share the layout because Lean shares the objects: a big natural number handed to integer code is
the same object, unchanged.

Two rules hold for every number that leaves this file. Compiled Lean depends on them (it decides that two
small numbers are equal by comparing the words), so a number that comes in breaking either one stops the
machine:

  - a natural number below 2^63 is a tagged word, never an object; so is an integer in the 32-bit range;
  - an object's top limb is not zero.

This file is the part that knows what a number is in memory: reading an argument, whether it came as a
tagged word or an object, and making a result that keeps the two rules. The arithmetic itself is in Lean
(Runtime/Big.lean), on arrays of limbs with every index checked: this file copies an argument's limbs into such
an array, calls it, and copies the answer out. Limbs are 32 bits so that everything in between fits in 64.

How long an operation takes depends on the numbers, as it does in Lean's runtime. Arithmetic on a secret
done through `Nat` or `Int` is not hidden from someone who can time it.

Each function returns what Lean's runtime (4.35.0, runtime/object.cpp over GMP) returns for the arguments
compiled Lean can pass it. Arguments are borrowed unless a comment says otherwise; results belong to the
caller.
*/
#include "big.h"

_Static_assert(sizeof(size_t) == 8 && sizeof(void *) == 8, "the number code is written for a 64-bit machine");
_Static_assert(sizeof(unsigned) == 4, "small integers are taken to be 32 bits");

#define LIMB_TOP 0x80000000u   /* the highest bit of a limb */

typedef struct {
    lean_object header;
    uint32_t negative;   /* 1 for a number below zero, otherwise 0 */
    uint32_t count;      /* how many limbs follow: at least one, and the last is not zero */
    uint32_t limbs[];    /* the number without its sign, least significant 32 bits first */
} big_object;

/* A number being read, wherever its limbs are: in an object, or in two limbs on the caller's stack when it
arrived as a tagged word. Zero has no limbs and is not negative; otherwise the top limb is not zero. */
typedef struct {
    uint32_t const * limbs;
    size_t count;
    bool negative;
} number;

/* ---- Reading arguments ---- */

/* The number with this magnitude (the number without its sign) and this sign. */
static number number_of_word(uint64_t magnitude, bool negative, uint32_t small[2]) {
    small[0] = (uint32_t)magnitude;
    small[1] = (uint32_t)(magnitude >> 32);
    number n = { small, small[1] != 0 ? 2 : small[0] != 0 ? 1 : 0, negative };
    return n;
}

/* An object handed in as a number. The checks here and in the two functions below cost a few comparisons
and can only fail if this file has a fault or memory has been damaged: nothing else makes these objects.
Carrying on would mean wrong arithmetic (compiled Lean and this file both take an object to be a number too
large for a tagged word), so the machine stops instead. */
static number number_of_object(b_lean_obj_arg o) {
    big_object const * big = (big_object const *)o;
    if (!lean_is_mpz(o) || big->count == 0 || big->limbs[big->count - 1] == 0 || big->negative > 1)
        rt_stop("something that is not a big number, or not a well-formed one, was used as a number");
    number n = { big->limbs, big->count, big->negative != 0 };
    return n;
}

/* A natural-number argument. `small` holds the limbs of one that arrived as a tagged word, so it has to live
as long as the result is used. An object has to be 2^63 or more. */
static number nat_view(b_lean_obj_arg o, uint32_t small[2]) {
    if (lean_is_scalar(o)) return number_of_word(lean_unbox(o), false, small);
    number n = number_of_object(o);
    if (n.negative || n.count < 2 || (n.count == 2 && n.limbs[1] < LIMB_TOP))
        rt_stop("an object used as a natural number holds a negative number or one below 2^63");
    return n;
}

/* An integer argument. An object has to be outside the 32-bit range. */
static number int_view(b_lean_obj_arg o, uint32_t small[2]) {
    if (lean_is_scalar(o)) {
        int value = lean_scalar_to_int(o);
        /* Negated as unsigned, so that the most negative value does not overflow. */
        return number_of_word(value < 0 ? 0u - (unsigned)value : (unsigned)value, value < 0, small);
    }
    number n = number_of_object(o);
    if (n.count == 1 && (n.limbs[0] < LIMB_TOP || (n.negative && n.limbs[0] == LIMB_TOP)))
        rt_stop("an object used as an integer holds a number that fits in 32 bits");
    return n;
}

/* ---- Making results ---- */

/* Room for `count` limbs while a result is worked out. Freed by the caller on every path. */
static uint32_t * limbs_new(size_t count) {
    return rt_malloc(lean_usize_mul_checked(count, sizeof(uint32_t)));
}

/* `count` without the zero limbs at the top. */
static size_t trimmed(uint32_t const * limbs, size_t count) {
    while (count > 0 && limbs[count - 1] == 0) count--;
    return count;
}

/* The object for a number that does not fit in a tagged word. Copies the limbs. */
static lean_object * big_new(bool negative, uint32_t const * limbs, size_t count) {
    assert(count > 0 && limbs[count - 1] != 0);
    if (count > UINT32_MAX) lean_internal_panic_out_of_memory();
    size_t bytes = lean_usize_add_checked(sizeof(big_object), lean_usize_mul_checked(count, sizeof(uint32_t)));
    big_object * o = (big_object *)lean_alloc_object(bytes);
    lean_set_st_header((lean_object *)o, LeanMPZ, 0);
    o->negative = negative ? 1 : 0;
    o->count = (uint32_t)count;
    memcpy(o->limbs, limbs, count * sizeof(uint32_t));
    return (lean_object *)o;
}

/* The natural number with these limbs as Lean holds it: a tagged word below 2^63, an object from there up. */
static lean_obj_res nat_result(uint32_t const * limbs, size_t count) {
    count = trimmed(limbs, count);
    if (count == 0) return lean_box(0);
    if (count == 1) return lean_box(limbs[0]);
    if (count == 2 && limbs[1] < LIMB_TOP) return lean_box(((size_t)limbs[1] << 32) | limbs[0]);
    return big_new(false, limbs, count);
}

/* The integer with this sign and these limbs as Lean holds it: a tagged word holding the 32 bits of a value
from -2^31 to 2^31 - 1, an object for anything else. */
static lean_obj_res int_result(bool negative, uint32_t const * limbs, size_t count) {
    count = trimmed(limbs, count);
    if (count == 0) return lean_box(0);
    if (count == 1) {
        uint32_t magnitude = limbs[0];
        if (!negative && magnitude < LIMB_TOP) return lean_box(magnitude);
        if (negative && magnitude <= LIMB_TOP) return lean_box((uint32_t)(0u - magnitude));
    }
    return big_new(negative, limbs, count);
}

/* The same, for limbs in a working buffer that is finished with. */
static lean_obj_res nat_result_freeing(uint32_t * limbs, size_t count) {
    lean_obj_res r = nat_result(limbs, count);
    rt_free(limbs);
    return r;
}

static lean_obj_res int_result_freeing(bool negative, uint32_t * limbs, size_t count) {
    lean_obj_res r = int_result(negative, limbs, count);
    rt_free(limbs);
    return r;
}

static lean_obj_res nat_of_word(uint64_t value) {
    uint32_t small[2];
    number n = number_of_word(value, false, small);
    return nat_result(n.limbs, n.count);
}

/* ---- Handing limbs to the arithmetic and taking them back ---- */

/* Runtime/Big.lean. Each takes the arrays it is given for its own and returns one that is the caller's. */
lean_object * rt_big_add(lean_object *, lean_object *);
lean_object * rt_big_sub(lean_object *, lean_object *);
lean_object * rt_big_mul(lean_object *, lean_object *);
lean_object * rt_big_div(lean_object *, lean_object *);
lean_object * rt_big_mod(lean_object *, lean_object *);
lean_object * rt_big_and(lean_object *, lean_object *);
lean_object * rt_big_or(lean_object *, lean_object *);
uint8_t rt_big_compare(lean_object *, lean_object *);
lean_object * rt_big_decimal(lean_object *, uint32_t);
lean_object * rt_big_shift_left(lean_object *, size_t);
lean_object * rt_big_shift_right(lean_object *, size_t);
lean_object * rt_big_power(lean_object *, size_t);
lean_object * rt_big_int_add(uint8_t, lean_object *, uint8_t, lean_object *);
lean_object * rt_big_int_mul(uint8_t, lean_object *, uint8_t, lean_object *);
lean_object * rt_big_int_ediv(uint8_t, lean_object *, uint8_t, lean_object *);
lean_object * rt_big_int_emod(uint8_t, lean_object *, lean_object *);
uint8_t rt_big_int_compare(uint8_t, lean_object *, uint8_t, lean_object *);

/* What rt_big_compare and rt_big_int_compare answer. */
enum { SMALLER = 0, EQUAL = 1, LARGER = 2 };

/* A number's limbs as the array the arithmetic takes. */
static lean_object * limbs_of(number n) {
    lean_object * array = lean_alloc_array(n.count, n.count);
    for (size_t i = 0; i < n.count; i++) lean_array_set_core(array, i, lean_box(n.limbs[i]));
    return array;
}

/* The limbs in an array the arithmetic returned, in a buffer the caller frees. Consumes the array. */
static uint32_t * limbs_from(lean_obj_arg array, size_t * count) {
    *count = lean_array_size(array);
    uint32_t * limbs = limbs_new(*count + 1);
    for (size_t i = 0; i < *count; i++) limbs[i] = (uint32_t)lean_unbox(lean_array_get_core(array, i));
    lean_dec(array);
    return limbs;
}

static lean_obj_res nat_from(lean_obj_arg array) {
    size_t count;
    uint32_t * limbs = limbs_from(array, &count);
    return nat_result_freeing(limbs, count);
}

/* An integer comes back as its limbs and then one more element, 1 if it is below zero. */
static lean_obj_res int_from(lean_obj_arg array) {
    size_t count;
    uint32_t * limbs = limbs_from(array, &count);
    if (count == 0) rt_stop("the arithmetic returned an integer without its sign");
    return int_result_freeing(limbs[count - 1] != 0, limbs, count - 1);
}

typedef lean_object * (*nat_operation)(lean_object *, lean_object *);
typedef lean_object * (*int_operation)(uint8_t, lean_object *, uint8_t, lean_object *);

static lean_obj_res nat_apply(nat_operation operation, b_lean_obj_arg a1, b_lean_obj_arg a2) {
    uint32_t small1[2], small2[2];
    lean_object * a = limbs_of(nat_view(a1, small1));
    return nat_from(operation(a, limbs_of(nat_view(a2, small2))));
}

static uint8_t nat_order(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    uint32_t small1[2], small2[2];
    lean_object * a = limbs_of(nat_view(a1, small1));
    return rt_big_compare(a, limbs_of(nat_view(a2, small2)));
}

/* `minus` turns the second number's sign round first: a - b is a + (-b), and zero stays as it is. */
static lean_obj_res int_apply(int_operation operation, b_lean_obj_arg a1, b_lean_obj_arg a2, bool minus) {
    uint32_t small1[2], small2[2];
    number a = int_view(a1, small1), b = int_view(a2, small2);
    if (minus && b.count != 0) b.negative = !b.negative;
    lean_object * limbs = limbs_of(a);
    return int_from(operation(a.negative, limbs, b.negative, limbs_of(b)));
}

static uint8_t int_order(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    uint32_t small1[2], small2[2];
    number a = int_view(a1, small1), b = int_view(a2, small2);
    lean_object * limbs = limbs_of(a);
    return rt_big_int_compare(a.negative, limbs, b.negative, limbs_of(b));
}

/* The position of the highest set bit; 0 for 0. */
static size_t mag_log2(number a) {
    if (a.count == 0) return 0;
    size_t result = (a.count - 1) * 32;
    for (uint32_t top = a.limbs[a.count - 1]; top >= 2; top /= 2) result++;
    return result;
}

/* The lowest 64 bits. */
static uint64_t mag_low64(number a) {
    uint64_t low = 0;
    if (a.count > 0) low = a.limbs[0];
    if (a.count > 1) low |= (uint64_t)a.limbs[1] << 32;
    return low;
}

/* ---- Natural numbers ---- */

/* A decimal literal. Compiled Lean writes every literal of 2^32 or more this way, each time the literal is
evaluated, so most of what arrives here is small after all. It passes digits and nothing else; anything but
digits stops the machine. */
lean_obj_res lean_cstr_to_nat(char const * digits) {
    if (digits[0] == 0) rt_stop("lean_cstr_to_nat was given no digits");
    lean_object * limbs = lean_alloc_array(0, 0);
    for (size_t at = 0; digits[at] != 0; at++) {
        if (digits[at] < '0' || digits[at] > '9') rt_stop("lean_cstr_to_nat was given something that is not a digit");
        limbs = rt_big_decimal(limbs, (uint32_t)(digits[at] - '0'));
    }
    return nat_from(limbs);
}

lean_obj_res lean_big_usize_to_nat(size_t n) {
    return nat_of_word(n);
}

lean_obj_res lean_big_uint64_to_nat(uint64_t n) {
    return nat_of_word(n);
}

lean_object * lean_nat_big_add(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_add, a1, a2);
}

/* Subtraction of natural numbers stops at zero. */
lean_object * lean_nat_big_sub(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_sub, a1, a2);
}

lean_object * lean_nat_big_mul(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_mul, a1, a2);
}

/* The product of two small numbers that does not fit in a tagged word. */
lean_object * lean_nat_overflow_mul(size_t a1, size_t a2) {
    uint32_t small1[2], small2[2];
    lean_object * a = limbs_of(number_of_word(a1, false, small1));
    return nat_from(rt_big_mul(a, limbs_of(number_of_word(a2, false, small2))));
}

/* In Lean, `n / 0 = 0`. */
lean_object * lean_nat_big_div(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_div, a1, a2);
}

/* In Lean, `n % 0 = n`. */
lean_object * lean_nat_big_mod(lean_object * a1, lean_object * a2) {
    if (a2 == lean_box(0)) {
        lean_inc(a1);
        return a1;
    }
    return nat_apply(rt_big_mod, a1, a2);
}

bool lean_nat_big_eq(lean_object * a1, lean_object * a2) {
    return nat_order(a1, a2) == EQUAL;
}

bool lean_nat_big_le(lean_object * a1, lean_object * a2) {
    return nat_order(a1, a2) != LARGER;
}

bool lean_nat_big_lt(lean_object * a1, lean_object * a2) {
    return nat_order(a1, a2) == SMALLER;
}

lean_object * lean_nat_big_land(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_and, a1, a2);
}

lean_object * lean_nat_big_lor(lean_object * a1, lean_object * a2) {
    return nat_apply(rt_big_or, a1, a2);
}

/* `a <<< shift`. */
lean_obj_res rt_big_nat_shiftl(b_lean_obj_arg a1, size_t shift) {
    uint32_t small[2];
    return nat_from(rt_big_shift_left(limbs_of(nat_view(a1, small)), shift));
}

/* `a1 >>> a2` when either is not small. */
lean_obj_res lean_nat_big_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    /* A shift of 2^63 or more leaves nothing of any number that fits in memory. */
    if (!lean_is_scalar(a2)) return lean_box(0);
    uint32_t small[2];
    number a = nat_view(a1, small);
    size_t shift = lean_unbox(a2);
    /* Lean's runtime shifts by at most 2^32 - 1 bits and refuses a longer shift that would leave something. */
    if (shift > UINT_MAX) {
        if (mag_log2(a) >= shift) lean_internal_panic("Nat.shiftr exponent is too big");
        return lean_box(0);
    }
    return nat_from(rt_big_shift_right(limbs_of(a), shift));
}

/* `a ^ exponent`. Anything to the power 0 is 1, zero included. */
lean_obj_res rt_big_nat_pow(b_lean_obj_arg a1, size_t exponent) {
    uint32_t small[2];
    return nat_from(rt_big_power(limbs_of(nat_view(a1, small)), exponent));
}

size_t rt_big_nat_log2(b_lean_obj_arg a) {
    uint32_t small[2];
    return mag_log2(nat_view(a, small));
}

size_t rt_big_nat_to_size(b_lean_obj_arg a) {
    uint32_t small[2];
    number n = nat_view(a, small);
    if (n.count > 2) lean_internal_panic_out_of_memory();
    return mag_low64(n);
}

/* ---- Integers ---- */

/* An integer that is known not to be negative, as a natural number. Consumes `a`. Lean's runtime does not
look at the sign and would hand back a negative natural number; that cannot be allowed to exist. */
lean_obj_res lean_big_int_to_nat(lean_obj_arg a) {
    uint32_t small[2];
    number n = int_view(a, small);
    if (n.negative) rt_stop("a negative integer was turned into a natural number");
    lean_obj_res r = nat_result(n.limbs, n.count);
    lean_dec(a);
    return r;
}

/* A natural number too large for a small integer, as an integer. */
lean_object * lean_big_size_t_to_int(size_t n) {
    uint32_t small[2];
    number value = number_of_word(n, false, small);
    return int_result(false, value.limbs, value.count);
}

lean_object * lean_big_int64_to_int(int64_t n) {
    uint32_t small[2];
    /* Negated as unsigned, so that the most negative value does not overflow. */
    number value = number_of_word(n < 0 ? 0 - (uint64_t)n : (uint64_t)n, n < 0, small);
    return int_result(value.negative, value.limbs, value.count);
}

lean_object * lean_int_big_neg(lean_object * a) {
    uint32_t small[2];
    number n = int_view(a, small);
    return int_result(!n.negative, n.limbs, n.count);
}

lean_object * lean_int_big_add(lean_object * a1, lean_object * a2) {
    return int_apply(rt_big_int_add, a1, a2, false);
}

lean_object * lean_int_big_sub(lean_object * a1, lean_object * a2) {
    return int_apply(rt_big_int_add, a1, a2, true);
}

lean_object * lean_int_big_mul(lean_object * a1, lean_object * a2) {
    return int_apply(rt_big_int_mul, a1, a2, false);
}

/* `Int.ediv` and `Int.emod`: the division whose remainder is never negative, `n = d * (n / d) + n % d` with
`0 <= n % d < |d|`, and `n / 0 = 0`, `n % 0 = n`. */
lean_object * lean_int_big_ediv(lean_object * a1, lean_object * a2) {
    return int_apply(rt_big_int_ediv, a1, a2, false);
}

lean_object * lean_int_big_emod(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number n = int_view(a1, small1), d = int_view(a2, small2);
    if (d.count == 0) {
        lean_inc(a1);
        return a1;
    }
    lean_object * limbs = limbs_of(n);
    return int_from(rt_big_int_emod(n.negative, limbs, limbs_of(d)));
}

bool lean_int_big_eq(lean_object * a1, lean_object * a2) {
    return int_order(a1, a2) == EQUAL;
}

bool lean_int_big_le(lean_object * a1, lean_object * a2) {
    return int_order(a1, a2) != LARGER;
}

bool lean_int_big_lt(lean_object * a1, lean_object * a2) {
    return int_order(a1, a2) == SMALLER;
}

/* ---- Fixed-width numbers from big ones ---- */

/* The number modulo 2^64, as a value from 0 to 2^64 - 1: for a negative number, what its two's complement
form keeps in 64 bits. The narrower types keep the low bits of this. */
static uint64_t modulo_2_64(b_lean_obj_arg a) {
    uint32_t small[2];
    number n = int_view(a, small);
    uint64_t low = mag_low64(n);
    return n.negative ? 0 - low : low;
}

uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a) {
    return (uint8_t)modulo_2_64(a);
}

uint16_t lean_uint16_of_big_nat(b_lean_obj_arg a) {
    return (uint16_t)modulo_2_64(a);
}

uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a) {
    return (uint32_t)modulo_2_64(a);
}

uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a) {
    return modulo_2_64(a);
}

/* Lean's runtime reads the lowest word of the magnitude here, without regard to sign. The argument is a
natural number, for which that is the same as the others. */
size_t lean_usize_of_big_nat(b_lean_obj_arg a) {
    uint32_t small[2];
    return mag_low64(int_view(a, small));
}

int64_t lean_int64_of_big_int(b_lean_obj_arg a) {
    return (int64_t)modulo_2_64(a);
}

ptrdiff_t lean_isize_of_big_int(b_lean_obj_arg a) {
    return (ptrdiff_t)(int64_t)modulo_2_64(a);
}
