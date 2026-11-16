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

The arithmetic is the kind done on paper, one limb at a time. Limbs are 32 bits so that everything in
between fits in 64: there is no 128-bit arithmetic here, for which a compiler calls a helper library that
bare metal does not have. Nothing recurses. Every working buffer comes from the allocator, which wipes it
when it is freed.

How long an operation takes depends on the numbers, as it does in Lean's runtime. Arithmetic on a secret
done through `Nat` or `Int` is not hidden from someone who can time it.

Each function returns what Lean's runtime (4.35.0, runtime/object.cpp over GMP) returns for the arguments
compiled Lean can pass it. Arguments are borrowed unless a comment says otherwise; results belong to the
caller.
*/
#include "big.h"

_Static_assert(sizeof(size_t) == 8 && sizeof(void *) == 8, "the number code is written for a 64-bit machine");
_Static_assert(sizeof(unsigned) == 4, "small integers are taken to be 32 bits");

#define LIMB_MAX 0xFFFFFFFFu
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

/* ---- Arithmetic on magnitudes: limbs without a sign ---- */

/* Which is larger: below zero if `a` is smaller than `b`, zero if they are equal, above zero if larger. */
static int mag_compare(number a, number b) {
    if (a.count != b.count) return a.count < b.count ? -1 : 1;
    for (size_t i = a.count; i-- > 0;) {
        if (a.limbs[i] != b.limbs[i]) return a.limbs[i] < b.limbs[i] ? -1 : 1;
    }
    return 0;
}

static size_t longer(number a, number b) {
    return a.count > b.count ? a.count : b.count;
}

/* r = a + b. Writes longer(a, b) + 1 limbs. */
static void mag_add(uint32_t * r, number a, number b) {
    size_t count = longer(a, b);
    uint64_t carry = 0;
    for (size_t i = 0; i < count; i++) {
        uint64_t sum = carry;
        if (i < a.count) sum += a.limbs[i];
        if (i < b.count) sum += b.limbs[i];
        r[i] = (uint32_t)sum;
        carry = sum >> 32;
    }
    r[count] = (uint32_t)carry;
}

/* r = a - b, where a is not smaller than b. Writes a.count limbs. `r` may be `b`'s own limbs. */
static void mag_sub(uint32_t * r, number a, number b) {
    uint64_t borrow = 0;
    for (size_t i = 0; i < a.count; i++) {
        /* At least -2^32, so if it went below zero and wrapped around, the top bit says so. */
        uint64_t difference = (uint64_t)a.limbs[i] - (i < b.count ? b.limbs[i] : 0) - borrow;
        r[i] = (uint32_t)difference;
        borrow = difference >> 63;
    }
    assert(borrow == 0);
}

/* r = a * b. Writes a.count + b.count limbs. `r` is neither argument's limbs. */
static void mag_mul(uint32_t * r, number a, number b) {
    memset(r, 0, (a.count + b.count) * sizeof(uint32_t));
    for (size_t i = 0; i < a.count; i++) {
        uint64_t carry = 0;
        for (size_t j = 0; j < b.count; j++) {
            /* At most (2^32 - 1)^2 + 2 (2^32 - 1) = 2^64 - 1. */
            uint64_t t = (uint64_t)a.limbs[i] * b.limbs[j] + r[i + j] + carry;
            r[i + j] = (uint32_t)t;
            carry = t >> 32;
        }
        r[i + b.count] = (uint32_t)carry;
    }
}

/* a * b in a new buffer for the caller to free; `*count` is its length without zero limbs at the top. */
static uint32_t * mag_mul_new(number a, number b, size_t * count) {
    size_t room = lean_usize_add_checked(a.count, b.count);
    uint32_t * r = limbs_new(room);
    mag_mul(r, a, b);
    *count = trimmed(r, room);
    return r;
}

/* r = a << bits for `count` limbs of `a`, with bits from 0 to 31. Writes `count` limbs and returns the bits
pushed out of the top. `r` may be `a`. */
static uint32_t shift_left_bits(uint32_t * r, uint32_t const * a, size_t count, unsigned bits) {
    uint32_t carry = 0;
    for (size_t i = 0; i < count; i++) {
        uint64_t wide = ((uint64_t)a[i] << bits) | carry;
        r[i] = (uint32_t)wide;
        carry = (uint32_t)(wide >> 32);
    }
    return carry;
}

/* r = a >> bits for `count` limbs of `a`, with bits from 0 to 31. Writes `count` limbs. `r` may be `a`. */
static void shift_right_bits(uint32_t * r, uint32_t const * a, size_t count, unsigned bits) {
    uint32_t fallen = 0;   /* the bits that fell off the limb above */
    for (size_t i = count; i-- > 0;) {
        uint32_t limb = a[i];
        r[i] = (uint32_t)((((uint64_t)fallen << 32) | limb) >> bits);
        fallen = limb & ((1u << bits) - 1);
    }
}

/* The position of the highest set bit; 0 for zero. */
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

/* Division by a single limb, a digit at a time from the top, as on paper. */
static void divide_by_limb(number a, uint32_t divisor, uint32_t * quotient, uint32_t * remainder) {
    uint64_t rest = 0;
    for (size_t i = a.count; i-- > 0;) {
        /* `rest` is below the divisor, so the quotient of this step fits a limb. */
        uint64_t part = (rest << 32) | a.limbs[i];
        quotient[i] = (uint32_t)(part / divisor);
        rest = part % divisor;
    }
    remainder[0] = (uint32_t)rest;
}

/*
Long division by two or more limbs: Knuth's algorithm D (The Art of Computer Programming, volume 2, section
4.3.1), with his step numbers. `a` has at least as many limbs as `b`.

Each quotient limb is guessed from the top two limbs of what is left and the top limb of the divisor. With
the divisor shifted so its top bit is set, the guess is never too small and at most two too large; a look
at one more limb of each (D3) catches nearly every overestimate, and the rare one that is left shows up as
a subtraction that goes below zero and is undone (D6).
*/
static void divide_long(number a, number b, uint32_t * quotient, uint32_t * remainder) {
    size_t m = a.count, n = b.count;
    /* D1: shift both so that the divisor's top bit is set. The dividend gets one more limb for what the
    shift pushes out. */
    unsigned shift = 0;
    while (((b.limbs[n - 1] << shift) & LIMB_TOP) == 0) shift++;
    uint32_t * v = limbs_new(n);
    uint32_t * u = limbs_new(lean_usize_add_checked(m, 1));
    shift_left_bits(v, b.limbs, n, shift);
    u[m] = shift_left_bits(u, a.limbs, m, shift);
    /* D2, D7: one quotient limb at a time, from the top. Throughout, u[j + n] is at most v[n - 1]. */
    for (size_t j = m - n + 1; j-- > 0;) {
        /* D3: guess. The guess can be 2^32 or 2^32 + 1, which no limb holds, so that is corrected first; it
        is at most 2^32 - 1 before it is multiplied, and `rest` is below 2^32 whenever it is shifted. */
        uint64_t top = ((uint64_t)u[j + n] << 32) | u[j + n - 1];
        uint64_t guess = top / v[n - 1];
        uint64_t rest = top % v[n - 1];
        while (guess > LIMB_MAX || guess * v[n - 2] > ((rest << 32) | u[j + n - 2])) {
            guess--;
            rest += v[n - 1];
            if (rest > LIMB_MAX) break;
        }
        assert(guess <= LIMB_MAX);
        /* D4: subtract guess * v from the n + 1 limbs of u starting at j. */
        uint64_t carry = 0, borrow = 0;
        for (size_t i = 0; i < n; i++) {
            /* At most (2^32 - 1)^2 + 2^32 - 1, which fits. */
            uint64_t product = guess * v[i] + carry;
            carry = product >> 32;
            /* At least -2^32, so the top bit says whether it went below zero, as in mag_sub. */
            uint64_t difference = (uint64_t)u[i + j] - (uint32_t)product - borrow;
            u[i + j] = (uint32_t)difference;
            borrow = difference >> 63;
        }
        uint64_t difference = (uint64_t)u[j + n] - carry - borrow;
        u[j + n] = (uint32_t)difference;
        /* D5, D6: if that went below zero the guess was one too large. Add v back; the carry out of the top
        cancels the borrow and is dropped. */
        if ((difference >> 63) != 0) {
            guess--;
            carry = 0;
            for (size_t i = 0; i < n; i++) {
                uint64_t sum = (uint64_t)u[i + j] + v[i] + carry;
                u[i + j] = (uint32_t)sum;
                carry = sum >> 32;
            }
            u[j + n] = (uint32_t)(u[j + n] + carry);
        }
        quotient[j] = (uint32_t)guess;
    }
    /* D8: what is left of u, shifted back, is the remainder. */
    shift_right_bits(remainder, u, n, shift);
    rt_free(u);
    rt_free(v);
}

/* quotient = a / b rounded down and remainder = a - quotient * b, for b other than zero. Writes a.count
limbs of quotient and b.count limbs of remainder, zero at the top where the value is shorter. */
static void mag_divide(number a, number b, uint32_t * quotient, uint32_t * remainder) {
    assert(b.count > 0);
    memset(quotient, 0, a.count * sizeof(uint32_t));
    memset(remainder, 0, b.count * sizeof(uint32_t));
    if (a.count < b.count) {
        memcpy(remainder, a.limbs, a.count * sizeof(uint32_t));
    } else if (b.count == 1) {
        divide_by_limb(a, b.limbs[0], quotient, remainder);
    } else {
        divide_long(a, b, quotient, remainder);
    }
}

/* ---- Natural numbers ---- */

/* A decimal literal. Compiled Lean writes every literal of 2^32 or more this way, each time the literal is
evaluated, so most of what arrives here is small after all. It passes digits and nothing else; anything but
digits stops the machine. (Lean's runtime hands the text to GMP, which would also skip spaces and take a
sign.) */
lean_obj_res lean_cstr_to_nat(char const * digits) {
    size_t length = strlen(digits);
    if (length == 0) rt_stop("lean_cstr_to_nat was given no digits");
    /* Eight decimal digits are below 2^32, so a limb for every eight digits, and one more, is enough. */
    size_t count = length / 8 + 1;
    uint32_t * limbs = limbs_new(count);
    memset(limbs, 0, count * sizeof(uint32_t));
    for (size_t at = 0; at < length; at++) {
        if (digits[at] < '0' || digits[at] > '9') rt_stop("lean_cstr_to_nat was given something that is not a digit");
        /* limbs = limbs * 10 + digit */
        uint64_t carry = (uint64_t)(digits[at] - '0');
        for (size_t i = 0; i < count; i++) {
            uint64_t t = (uint64_t)limbs[i] * 10 + carry;
            limbs[i] = (uint32_t)t;
            carry = t >> 32;
        }
        assert(carry == 0);
    }
    return nat_result_freeing(limbs, count);
}

lean_obj_res lean_big_usize_to_nat(size_t n) {
    return nat_of_word(n);
}

lean_obj_res lean_big_uint64_to_nat(uint64_t n) {
    return nat_of_word(n);
}

lean_object * lean_nat_big_add(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    size_t count = lean_usize_add_checked(longer(a, b), 1);
    uint32_t * r = limbs_new(count);
    mag_add(r, a, b);
    return nat_result_freeing(r, count);
}

/* Subtraction of natural numbers stops at zero. */
lean_object * lean_nat_big_sub(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    if (mag_compare(a, b) <= 0) return lean_box(0);
    uint32_t * r = limbs_new(a.count);
    mag_sub(r, a, b);
    return nat_result_freeing(r, a.count);
}

lean_object * lean_nat_big_mul(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    size_t count;
    uint32_t * r = mag_mul_new(a, b, &count);
    return nat_result_freeing(r, count);
}

/* The product of two small numbers that does not fit in a tagged word. */
lean_object * lean_nat_overflow_mul(size_t a1, size_t a2) {
    uint32_t small1[2], small2[2], r[4];
    number a = number_of_word(a1, false, small1), b = number_of_word(a2, false, small2);
    mag_mul(r, a, b);
    return nat_result(r, a.count + b.count);
}

/* In Lean, `n / 0 = 0`. */
lean_object * lean_nat_big_div(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    if (b.count == 0) return lean_box(0);
    uint32_t * quotient = limbs_new(a.count);
    uint32_t * remainder = limbs_new(b.count);
    mag_divide(a, b, quotient, remainder);
    rt_free(remainder);
    return nat_result_freeing(quotient, a.count);
}

/* In Lean, `n % 0 = n`. */
lean_object * lean_nat_big_mod(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    if (b.count == 0) {
        lean_inc(a1);
        return a1;
    }
    uint32_t * quotient = limbs_new(a.count);
    uint32_t * remainder = limbs_new(b.count);
    mag_divide(a, b, quotient, remainder);
    rt_free(quotient);
    return nat_result_freeing(remainder, b.count);
}

bool lean_nat_big_eq(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return mag_compare(nat_view(a1, small1), nat_view(a2, small2)) == 0;
}

bool lean_nat_big_le(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return mag_compare(nat_view(a1, small1), nat_view(a2, small2)) <= 0;
}

bool lean_nat_big_lt(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return mag_compare(nat_view(a1, small1), nat_view(a2, small2)) < 0;
}

lean_object * lean_nat_big_land(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    size_t count = a.count < b.count ? a.count : b.count;
    uint32_t * r = limbs_new(count);
    for (size_t i = 0; i < count; i++) r[i] = a.limbs[i] & b.limbs[i];
    return nat_result_freeing(r, count);
}

lean_object * lean_nat_big_lor(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = nat_view(a1, small1), b = nat_view(a2, small2);
    size_t count = longer(a, b);
    uint32_t * r = limbs_new(count);
    for (size_t i = 0; i < count; i++) r[i] = (i < a.count ? a.limbs[i] : 0) | (i < b.count ? b.limbs[i] : 0);
    return nat_result_freeing(r, count);
}

/* `a <<< shift`: whole limbs of zeros at the bottom, then the rest of the shift within limbs. */
lean_obj_res rt_big_nat_shiftl(b_lean_obj_arg a1, size_t shift) {
    uint32_t small[2];
    number a = nat_view(a1, small);
    size_t whole = shift / 32;
    unsigned bits = (unsigned)(shift % 32);
    size_t count = lean_usize_add_checked(lean_usize_add_checked(a.count, whole), 1);
    uint32_t * r = limbs_new(count);
    memset(r, 0, whole * sizeof(uint32_t));
    r[count - 1] = shift_left_bits(r + whole, a.limbs, a.count, bits);
    return nat_result_freeing(r, count);
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
    size_t whole = shift / 32;
    unsigned bits = (unsigned)(shift % 32);
    if (whole >= a.count) return lean_box(0);
    size_t count = a.count - whole;
    uint32_t * r = limbs_new(count);
    shift_right_bits(r, a.limbs + whole, count, bits);
    return nat_result_freeing(r, count);
}

/* `a ^ exponent` by squaring: `power` runs through a, a^2, a^4, ... and `result` gathers the ones the
exponent's bits pick out. Anything to the power 0 is 1, zero included. */
lean_obj_res rt_big_nat_pow(b_lean_obj_arg a1, size_t exponent) {
    uint32_t small[2];
    number a = nat_view(a1, small);
    size_t result_count = 1, power_count = a.count;
    uint32_t * result = limbs_new(1);
    uint32_t * power = limbs_new(a.count);
    result[0] = 1;
    memcpy(power, a.limbs, a.count * sizeof(uint32_t));
    while (exponent != 0) {
        number p = { power, power_count, false };
        if ((exponent & 1) != 0) {
            number r = { result, result_count, false };
            uint32_t * product = mag_mul_new(r, p, &result_count);
            rt_free(result);
            result = product;
        }
        exponent >>= 1;
        if (exponent != 0) {
            uint32_t * square = mag_mul_new(p, p, &power_count);
            rt_free(power);
            power = square;
        }
    }
    rt_free(power);
    return nat_result_freeing(result, result_count);
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

/* a + b. With the same sign the magnitudes add; with different signs the smaller comes off the larger,
whose sign the result takes. */
static lean_obj_res int_add(number a, number b) {
    if (a.negative == b.negative) {
        size_t count = lean_usize_add_checked(longer(a, b), 1);
        uint32_t * r = limbs_new(count);
        mag_add(r, a, b);
        return int_result_freeing(a.negative, r, count);
    }
    int order = mag_compare(a, b);
    if (order == 0) return lean_box(0);
    if (order < 0) {
        number swap = a;
        a = b;
        b = swap;
    }
    uint32_t * r = limbs_new(a.count);
    mag_sub(r, a, b);
    return int_result_freeing(a.negative, r, a.count);
}

lean_object * lean_int_big_neg(lean_object * a) {
    uint32_t small[2];
    number n = int_view(a, small);
    return int_result(!n.negative, n.limbs, n.count);
}

lean_object * lean_int_big_add(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return int_add(int_view(a1, small1), int_view(a2, small2));
}

lean_object * lean_int_big_sub(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = int_view(a1, small1), b = int_view(a2, small2);
    /* a - b is a + (-b); zero stays as it is. */
    if (b.count != 0) b.negative = !b.negative;
    return int_add(a, b);
}

lean_object * lean_int_big_mul(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number a = int_view(a1, small1), b = int_view(a2, small2);
    size_t count;
    uint32_t * r = mag_mul_new(a, b, &count);
    return int_result_freeing(a.negative != b.negative, r, count);
}

/*
`Int.ediv` and `Int.emod`: the division whose remainder is never negative, `n = d * (n / d) + n % d` with
`0 <= n % d < |d|`, and `n / 0 = 0`, `n % 0 = n`.

Dividing the magnitudes gives |n| = |d| * q + r with 0 <= r < |d|. If n is not negative, or r is zero,
the quotient is q with the sign the signs of n and d give it, and the remainder is r. Otherwise n = -|d| q
- r = -|d| (q + 1) + (|d| - r): the quotient's magnitude is q + 1, with the same rule for its sign, and the
remainder is |d| - r. (Lean's runtime gets there by dividing towards zero and then correcting a negative
remainder; this is the same thing said in magnitudes.)
*/
lean_object * lean_int_big_ediv(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number n = int_view(a1, small1), d = int_view(a2, small2);
    if (d.count == 0) return lean_box(0);
    /* One limb more than the quotient needs, for the q + 1 above. */
    size_t count = lean_usize_add_checked(n.count, 1);
    uint32_t * quotient = limbs_new(count);
    uint32_t * remainder = limbs_new(d.count);
    mag_divide(n, d, quotient, remainder);
    quotient[n.count] = 0;
    if (n.negative && trimmed(remainder, d.count) != 0) {
        for (size_t i = 0; i < count; i++) {
            if (++quotient[i] != 0) break;
        }
    }
    rt_free(remainder);
    return int_result_freeing(n.negative != d.negative, quotient, count);
}

lean_object * lean_int_big_emod(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    number n = int_view(a1, small1), d = int_view(a2, small2);
    if (d.count == 0) {
        lean_inc(a1);
        return a1;
    }
    uint32_t * quotient = limbs_new(n.count);
    uint32_t * remainder = limbs_new(d.count);
    mag_divide(n, d, quotient, remainder);
    rt_free(quotient);
    number r = { remainder, trimmed(remainder, d.count), false };
    if (n.negative && r.count != 0) mag_sub(remainder, d, r);
    return int_result_freeing(false, remainder, d.count);
}

/* Below zero if `a` is less than `b`, zero if they are equal, above zero if greater. */
static int int_compare(number a, number b) {
    if (a.negative != b.negative) return a.negative ? -1 : 1;
    int order = mag_compare(a, b);
    return a.negative ? -order : order;
}

bool lean_int_big_eq(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return int_compare(int_view(a1, small1), int_view(a2, small2)) == 0;
}

bool lean_int_big_le(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return int_compare(int_view(a1, small1), int_view(a2, small2)) <= 0;
}

bool lean_int_big_lt(lean_object * a1, lean_object * a2) {
    uint32_t small1[2], small2[2];
    return int_compare(int_view(a1, small1), int_view(a2, small2)) < 0;
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
