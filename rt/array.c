/*
Arrays and byte arrays.

Both grow in place when the caller holds the only reference and there is room, and are copied otherwise.
An array or byte array marked linear (`markLinear`, which is how a secret is kept from being duplicated)
stops the machine if it would have to be copied because someone else still holds it. Lean's own runtime
only does that when asked through an environment variable.
*/
#include "rt.h"

/* Init's own conversions between lists and arrays, compiled Lean that the runtime calls back into. */
lean_object * lean_list_to_array(lean_object * type, lean_object * list);
lean_object * lean_array_to_list_impl(lean_object * type, lean_object * array);

static void refuse_copy_of_linear(b_lean_obj_arg o) {
    if (lean_is_marked_linear_core(o)) rt_stop("a value marked linear was used where it would have to be copied");
}

/* ---- Arrays of objects ---- */

lean_object * lean_array_mk(lean_obj_arg list) {
    return lean_list_to_array(lean_box(0), list);
}

lean_object * lean_array_to_list(lean_obj_arg a) {
    return lean_array_to_list_impl(lean_box(0), a);
}

/* A copy of `a` with the same elements, and room to grow if `expand`. Consumes `a`. */
lean_obj_res lean_copy_expand_array(lean_obj_arg a, bool expand) {
    size_t size = lean_array_size(a);
    size_t capacity = lean_array_capacity(a);
    if (expand) capacity = lean_usize_mul_checked(lean_usize_add_checked(capacity, 1), 2);
    lean_object * r = lean_alloc_array(size, capacity);
    if (lean_is_marked_linear_core(a)) lean_mark_linear_core(r);
    lean_object ** from = lean_array_cptr(a);
    lean_object ** to = lean_array_cptr(r);
    if (lean_is_exclusive(a)) {
        memcpy(to, from, size * sizeof(lean_object *));
        lean_free_object(a);
    } else {
        for (size_t i = 0; i < size; i++) {
            to[i] = from[i];
            lean_inc(to[i]);
        }
        lean_dec(a);
    }
    return r;
}

lean_obj_res lean_copy_expand_array_nonlinear(lean_obj_arg a, bool expand) {
    refuse_copy_of_linear(a);
    return lean_copy_expand_array(a, expand);
}

lean_object * lean_array_push(lean_obj_arg a, lean_obj_arg v) {
    lean_object * r;
    if (lean_is_exclusive(a)) {
        r = lean_array_capacity(a) > lean_array_size(a) ? a : lean_copy_expand_array(a, true);
    } else {
        r = lean_copy_expand_array_nonlinear(a, lean_array_capacity(a) < 2 * lean_array_size(a) + 1);
    }
    lean_array_object * array = lean_to_array(r);
    array->m_data[array->m_size] = v;
    array->m_size++;
    return r;
}

/* ---- Byte arrays ---- */

/* A copy of `a` with room for `capacity` elements. Consumes `a`. */
static lean_obj_res copy_sarray(lean_obj_arg a, size_t capacity) {
    unsigned element = lean_sarray_elem_size(a);
    size_t size = lean_sarray_size(a);
    lean_object * r = lean_alloc_sarray(element, size, capacity);
    if (lean_is_marked_linear_core(a)) lean_mark_linear_core(r);
    memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), element * size);
    lean_dec(a);
    return r;
}

/* `a` with room for at least `least` elements; twice that when it has to grow and `exact` is false. */
static lean_obj_res sarray_with_capacity(lean_obj_arg a, size_t least, bool exact) {
    if (least <= lean_sarray_capacity(a)) return a;
    size_t capacity = exact ? least : lean_usize_mul_checked(least, 2);
    if (!lean_is_exclusive(a)) refuse_copy_of_linear(a);
    return copy_sarray(a, capacity);
}

/* `a` if the caller holds the only reference, otherwise a copy that it does. */
static lean_obj_res sarray_exclusive(lean_obj_arg a) {
    if (lean_is_exclusive(a)) return a;
    refuse_copy_of_linear(a);
    return copy_sarray(a, lean_sarray_capacity(a));
}

lean_obj_res lean_byte_array_push(lean_obj_arg a, uint8_t b) {
    lean_object * r = sarray_exclusive(sarray_with_capacity(a, lean_usize_add_checked(lean_sarray_size(a), 1), false));
    lean_sarray_object * bytes = lean_to_sarray(r);
    bytes->m_data[bytes->m_size] = b;
    bytes->m_size++;
    return r;
}

/* `ByteArray.copySlice`: `len` bytes of `src` from `src_off` written over `dest` from `dest_off`, extending
`dest` if they run past its end. Offsets and lengths past the ends are clamped the way Lean specifies. */
lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg src, lean_obj_arg o_src_off, lean_obj_arg dest,
                                        lean_obj_arg o_dest_off, lean_obj_arg o_len, bool exact) {
    size_t src_size = lean_sarray_size(src);
    size_t dest_size = lean_sarray_size(dest);
    /* The three numbers are the caller's to give away. They are small unless someone passes 2^63 or more. */
    size_t src_off = rt_nat_to_size(o_src_off);
    size_t len = rt_nat_to_size(o_len);
    size_t dest_off = rt_nat_to_size(o_dest_off);
    lean_dec(o_src_off);
    lean_dec(o_len);
    lean_dec(o_dest_off);
    if (src_off > src_size) return dest;
    if (len > src_size - src_off) len = src_size - src_off;
    if (dest_off > dest_size) dest_off = dest_size;
    size_t new_size = lean_usize_add_checked(dest_off, len);
    if (new_size < dest_size) new_size = dest_size;
    lean_object * r = sarray_exclusive(sarray_with_capacity(dest, new_size, exact));
    lean_to_sarray(r)->m_size = new_size;
    /* `r` is held by no one else, so it cannot be `src` and the ranges cannot overlap. */
    memcpy(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
    return r;
}

/* ---- The rest of what compiled Lean asks of arrays ---- */

/* `Array.replicate`: `n` references to `v`. Consumes both. */
lean_object * lean_mk_array(lean_obj_arg n, lean_obj_arg v) {
    size_t size = rt_nat_to_size(n);
    lean_dec(n);
    lean_object * r = lean_alloc_array(size, size);
    lean_object ** to = lean_array_cptr(r);
    for (size_t i = 0; i < size; i++) to[i] = v;
    if (size == 0) {
        lean_dec(v);
    } else if (size > 1) {
        lean_inc_n(v, size - 1);
    }
    return r;
}

/* `a[i]!` and `a.set! i v` with `i` out of bounds: a Lean panic, which here stops the machine. */
lean_obj_res lean_array_get_panic(lean_obj_arg def_val) {
    return lean_panic_fn(def_val, lean_mk_string("Error: index out of bounds"));
}

lean_obj_res lean_array_set_panic(lean_obj_arg a, lean_obj_arg v) {
    lean_dec(v);
    return lean_panic_fn(a, lean_mk_string("Error: index out of bounds"));
}

/* `ByteArray.mk`: the bytes of an `Array UInt8`. Consumes it. */
lean_obj_res lean_byte_array_mk(lean_obj_arg a) {
    size_t size = lean_array_size(a);
    lean_object * r = lean_alloc_sarray(1, size, size);
    lean_object ** from = lean_array_cptr(a);
    uint8_t * to = lean_sarray_cptr(r);
    for (size_t i = 0; i < size; i++) to[i] = (uint8_t)lean_unbox(from[i]);
    lean_dec(a);
    return r;
}

/* `ByteArray.data`: the bytes as an `Array UInt8`. Consumes it. */
lean_obj_res lean_byte_array_data(lean_obj_arg a) {
    size_t size = lean_sarray_size(a);
    lean_object * r = lean_alloc_array(size, size);
    uint8_t * from = lean_sarray_cptr(a);
    lean_object ** to = lean_array_cptr(r);
    for (size_t i = 0; i < size; i++) to[i] = lean_box(from[i]);
    lean_dec(a);
    return r;
}

uint64_t lean_byte_array_hash(b_lean_obj_arg a) {
    return rt_hash_bytes(lean_sarray_cptr(a), lean_sarray_size(a), 11);
}

/* Equality of two scalar arrays already known to have the same number of elements. */
bool lean_sarray_eq_cold(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return memcmp(lean_sarray_cptr(a1), lean_sarray_cptr(a2), lean_sarray_elem_size(a1) * lean_sarray_size(a1)) == 0;
}

/* A copy of a scalar array someone else also holds, which compiled Lean asks for before changing it. */
lean_obj_res lean_copy_sarray_nonlinear(lean_obj_arg a, size_t capacity) {
    refuse_copy_of_linear(a);
    return copy_sarray(a, capacity);
}
