/*
Calling closures.

A closure is a function, the number of arguments it takes, and the arguments it already has. Applying it to
more arguments either still leaves it short (a new closure with more arguments fixed), completes it (call
the function), or over-completes it (call the function, then apply what it returns to the rest).

Functions of up to sixteen arguments take them as separate C arguments; above that they take one array.
Lean's runtime writes every combination out by hand for speed. This is the same behaviour in one function.
*/
#include "rt.h"

typedef lean_object obj;

static obj * call(void * fn, unsigned arity, obj ** a) {
    switch (arity) {
    case 1: return ((obj * (*)(obj *))fn)(a[0]);
    case 2: return ((obj * (*)(obj *, obj *))fn)(a[0], a[1]);
    case 3: return ((obj * (*)(obj *, obj *, obj *))fn)(a[0], a[1], a[2]);
    case 4: return ((obj * (*)(obj *, obj *, obj *, obj *))fn)(a[0], a[1], a[2], a[3]);
    case 5: return ((obj * (*)(obj *, obj *, obj *, obj *, obj *))fn)(a[0], a[1], a[2], a[3], a[4]);
    case 6: return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *))fn)(a[0], a[1], a[2], a[3], a[4], a[5]);
    case 7:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
    case 8:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    case 9:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8]);
    case 10:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9]);
    case 11:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]);
    case 12:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11]);
    case 13:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *,
                           obj *))fn)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12]);
    case 14:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *,
                           obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13]);
    case 15:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *,
                           obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14]);
    case 16:
        return ((obj * (*)(obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *, obj *,
                           obj *, obj *, obj *, obj *))fn)(
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15]);
    default: return ((obj * (*)(obj **))fn)(a);
    }
}

/* `f` with `n` more arguments fixed, still short of its arity. Consumes `f` and the arguments. */
static obj * fix_more(obj * f, unsigned n, obj ** as) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    obj * r = lean_alloc_closure(lean_closure_fun(f), arity, fixed + n);
    obj ** from = lean_closure_arg_cptr(f);
    obj ** to = lean_closure_arg_cptr(r);
    if (lean_is_exclusive(f)) {
        for (unsigned i = 0; i < fixed; i++) to[i] = from[i];
        lean_free_object(f);
    } else {
        for (unsigned i = 0; i < fixed; i++) {
            to[i] = from[i];
            lean_inc(to[i]);
        }
        lean_dec_ref(f);
    }
    for (unsigned i = 0; i < n; i++) to[fixed + i] = as[i];
    return r;
}

/* Applies `f` to `n` arguments. Consumes `f` and the arguments. */
obj * lean_apply_n(obj * f, unsigned n, obj ** as) {
    for (;;) {
        if (lean_is_scalar(f)) {
            /* An erased proof stands where a function would be: there is nothing to call. */
            for (unsigned i = 0; i < n; i++) lean_dec(as[i]);
            return f;
        }
        unsigned arity = lean_closure_arity(f);
        unsigned fixed = lean_closure_num_fixed(f);
        if (fixed + n < arity) return fix_more(f, n, as);
        unsigned taken = arity - fixed;
        void * fn = lean_closure_fun(f);
        obj * args[arity];
        obj ** held = lean_closure_arg_cptr(f);
        if (lean_is_exclusive(f)) {
            for (unsigned i = 0; i < fixed; i++) args[i] = held[i];
            lean_free_object(f);
        } else {
            for (unsigned i = 0; i < fixed; i++) {
                args[i] = held[i];
                lean_inc(args[i]);
            }
            lean_dec_ref(f);
        }
        for (unsigned i = 0; i < taken; i++) args[fixed + i] = as[i];
        obj * r = call(fn, arity, args);
        if (taken == n) return r;
        f = r;
        as += taken;
        n -= taken;
    }
}

obj * lean_apply_m(obj * f, unsigned n, obj ** as) {
    return lean_apply_n(f, n, as);
}

obj * lean_apply_1(obj * f, obj * a1) {
    obj * as[] = { a1 };
    return lean_apply_n(f, 1, as);
}
obj * lean_apply_2(obj * f, obj * a1, obj * a2) {
    obj * as[] = { a1, a2 };
    return lean_apply_n(f, 2, as);
}
obj * lean_apply_3(obj * f, obj * a1, obj * a2, obj * a3) {
    obj * as[] = { a1, a2, a3 };
    return lean_apply_n(f, 3, as);
}
obj * lean_apply_4(obj * f, obj * a1, obj * a2, obj * a3, obj * a4) {
    obj * as[] = { a1, a2, a3, a4 };
    return lean_apply_n(f, 4, as);
}
obj * lean_apply_5(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5) {
    obj * as[] = { a1, a2, a3, a4, a5 };
    return lean_apply_n(f, 5, as);
}
obj * lean_apply_6(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6) {
    obj * as[] = { a1, a2, a3, a4, a5, a6 };
    return lean_apply_n(f, 6, as);
}
obj * lean_apply_7(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7 };
    return lean_apply_n(f, 7, as);
}
obj * lean_apply_8(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8 };
    return lean_apply_n(f, 8, as);
}
obj * lean_apply_9(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                   obj * a9) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9 };
    return lean_apply_n(f, 9, as);
}
obj * lean_apply_10(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
    return lean_apply_n(f, 10, as);
}
obj * lean_apply_11(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
    return lean_apply_n(f, 11, as);
}
obj * lean_apply_12(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11, obj * a12) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
    return lean_apply_n(f, 12, as);
}
obj * lean_apply_13(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11, obj * a12, obj * a13) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
    return lean_apply_n(f, 13, as);
}
obj * lean_apply_14(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11, obj * a12, obj * a13, obj * a14) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
    return lean_apply_n(f, 14, as);
}
obj * lean_apply_15(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11, obj * a12, obj * a13, obj * a14, obj * a15) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
    return lean_apply_n(f, 15, as);
}
obj * lean_apply_16(obj * f, obj * a1, obj * a2, obj * a3, obj * a4, obj * a5, obj * a6, obj * a7, obj * a8,
                    obj * a9, obj * a10, obj * a11, obj * a12, obj * a13, obj * a14, obj * a15, obj * a16) {
    obj * as[] = { a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
    return lean_apply_n(f, 16, as);
}
