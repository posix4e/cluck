/*
Strings.

A string is its UTF-8 bytes with a terminating zero, the byte count including that zero, and the number of
characters. Appending grows in place when the caller holds the only reference and there is room.
*/
#include "rt.h"

static lean_object * new_string(size_t size, size_t capacity, size_t length) {
    lean_string_object * o =
        (lean_string_object *)lean_alloc_object(lean_usize_add_checked(sizeof(lean_string_object), capacity));
    lean_set_st_header((lean_object *)o, LeanString, 0);
    o->m_size = size;
    o->m_capacity = capacity;
    o->m_length = length;
    return (lean_object *)o;
}

static char * string_bytes(lean_object * s) {
    return lean_to_string(s)->m_data;
}

/* The rules of UTF-8 are in Lean (Runtime/Utf8.lean). This file knows where a string's bytes are and how
many there are; it hands over the bytes in question, as numbers, and acts on the answer. */
uint8_t rt_utf8_strict(uint8_t, uint8_t, uint8_t, uint8_t, size_t);
uint64_t rt_utf8_read(uint8_t, uint8_t, uint8_t, uint8_t, size_t);
uint64_t rt_utf8_write(uint32_t);
uint8_t rt_utf8_claims(uint8_t, uint8_t);

/* Byte `i` of the `size` bytes at `s`, or zero past the end. */
static uint8_t byte_at(char const * s, size_t size, size_t i) {
    return i < size ? (uint8_t)s[i] : 0;
}

/* The number of characters in `size` bytes of well-formed UTF-8, or false if they are not well-formed. */
static bool utf8_length(char const * s, size_t size, size_t * length) {
    size_t count = 0;
    for (size_t at = 0; at < size; count++) {
        uint8_t taken = rt_utf8_strict(byte_at(s, size, at), byte_at(s, size, at + 1), byte_at(s, size, at + 2),
                                       byte_at(s, size, at + 3), size - at);
        if (taken == 0) return false;
        at += taken;
    }
    *length = count;
    return true;
}

static unsigned scalar_size(uint32_t c) {
    return (unsigned)(rt_utf8_write(c) >> 32);
}

/* The UTF-8 encoding of `c` written at `to`; returns how many bytes that was (one to four). */
static unsigned put_scalar(char * to, uint32_t c) {
    uint64_t encoded = rt_utf8_write(c);
    unsigned count = (unsigned)(encoded >> 32);
    for (unsigned i = 0; i < count; i++) to[i] = (char)(encoded >> (8 * i));
    return count;
}

lean_object * lean_mk_string_unchecked(char const * s, size_t size, size_t length) {
    size_t with_zero = lean_usize_add_checked(size, 1);
    lean_object * r = new_string(with_zero, with_zero, length);
    memcpy(string_bytes(r), s, size);
    string_bytes(r)[size] = 0;
    return r;
}

/* A string from a C string. Compiled Lean passes its own literals here, which are UTF-8; anything else stops
the machine. (Lean's runtime repairs bad bytes with U+FFFD; nothing here should ever need that.) */
lean_object * lean_mk_string(char const * s) {
    size_t size = strlen(s);
    size_t length;
    if (!utf8_length(s, size, &length)) rt_stop("lean_mk_string was given bytes that are not UTF-8");
    return lean_mk_string_unchecked(s, size, length);
}

/* `String.mk`: a string from a list of characters. Consumes the list. */
lean_obj_res lean_string_mk(lean_obj_arg chars) {
    size_t size = 0, length = 0;
    for (lean_object * at = chars; !lean_is_scalar(at); at = lean_ctor_get(at, 1)) {
        size = lean_usize_add_checked(size, scalar_size(lean_unbox_uint32(lean_ctor_get(at, 0))));
        length++;
    }
    size_t with_zero = lean_usize_add_checked(size, 1);
    lean_object * r = new_string(with_zero, with_zero, length);
    char * to = string_bytes(r);
    for (lean_object * at = chars; !lean_is_scalar(at); at = lean_ctor_get(at, 1))
        to += put_scalar(to, lean_unbox_uint32(lean_ctor_get(at, 0)));
    *to = 0;
    lean_dec(chars);
    return r;
}

/* A copy of `s` with room for `capacity` bytes. Consumes `s`. */
static lean_obj_res copy_string(lean_obj_arg s, size_t capacity) {
    size_t size = lean_string_size(s);
    lean_object * r = new_string(size, capacity, lean_string_len(s));
    if (lean_is_marked_linear_core(s)) lean_mark_linear_core(r);
    memcpy(string_bytes(r), lean_string_cstr(s), size);
    lean_dec_ref(s);
    return r;
}

/* `s`, held by the caller alone, with room for `extra` more bytes. */
static lean_object * string_with_room(lean_object * s, size_t extra) {
    size_t size = lean_string_size(s);
    size_t capacity = lean_string_capacity(s);
    size_t needed = lean_usize_add_checked(size, extra);
    if (needed <= capacity) return s;
    lean_object * r = new_string(size, lean_usize_add_checked(capacity, needed), lean_string_len(s));
    if (lean_is_marked_linear_core(s)) lean_mark_linear_core(r);
    memcpy(string_bytes(r), lean_string_cstr(s), size);
    lean_free_object(s);
    return r;
}

/* `s1 ++ s2`. Consumes `s1`, borrows `s2`. */
lean_object * lean_string_append(lean_object * s1, lean_object * s2) {
    size_t size1 = lean_string_size(s1);
    size_t size2 = lean_string_size(s2);
    size_t new_length = lean_string_len(s1) + lean_string_len(s2);
    size_t new_size = lean_usize_add_checked(size1, size2) - 1;
    lean_object * r;
    if (!lean_is_exclusive(s1)) {
        if (lean_is_marked_linear_core(s1)) rt_stop("a value marked linear was used where it would have to be copied");
        r = copy_string(s1, lean_usize_mul_checked(new_size, 2));
    } else {
        r = string_with_room(s1, size2 - 1);
    }
    memcpy(string_bytes(r) + size1 - 1, lean_string_cstr(s2), size2 - 1);
    lean_to_string(r)->m_size = new_size;
    lean_to_string(r)->m_length = new_length;
    string_bytes(r)[new_size - 1] = 0;
    return r;
}

/* Equality of two strings already known to have the same byte count. */
bool lean_string_eq_cold(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    return memcmp(lean_string_cstr(s1), lean_string_cstr(s2), lean_string_size(s1)) == 0;
}

/* A number in decimal. */
lean_obj_res lean_string_of_usize(size_t n) {
    char digits[24];
    size_t at = sizeof(digits);
    do {
        digits[--at] = (char)('0' + n % 10);
        n /= 10;
    } while (n != 0);
    return lean_mk_string_unchecked(digits + at, sizeof(digits) - at, sizeof(digits) - at);
}

/* ---- Characters by byte position ----

Lean addresses a character by the byte offset where its UTF-8 encoding starts, and defines what happens at
offsets that are out of range or in the middle of a character. The rules below are Lean's, case for case. */

/* The character whose encoding starts at byte `i` of the `size` bytes at `str`, if one does. */
static bool char_at(char const * str, size_t size, size_t i, uint32_t * result) {
    uint64_t found = rt_utf8_read(byte_at(str, size, i), byte_at(str, size, i + 1), byte_at(str, size, i + 2),
                                  byte_at(str, size, i + 3), size - i);
    *result = (uint32_t)found;
    return (found >> 32) != 0;
}

/* `String.get`: the character at byte position `i`, or the default character if there is none. A position
that is not a small number is past the end of any string that can exist. */
uint32_t lean_string_utf8_get(b_lean_obj_arg s, b_lean_obj_arg i0) {
    if (!lean_is_scalar(i0)) return lean_char_default_value();
    size_t i = lean_unbox(i0);
    size_t size = lean_string_size(s) - 1;
    if (i >= size) return lean_char_default_value();
    uint32_t result;
    if (char_at(lean_string_cstr(s), size, i, &result)) return result;
    return lean_char_default_value();
}

/* The slow half of the inline `String.get`: `c` is the byte at `i` and is not ASCII. */
uint32_t lean_string_utf8_get_fast_cold(char const * str, size_t i, size_t size, unsigned char c) {
    uint32_t result;
    if ((c & 0x80) != 0 && char_at(str, size, i, &result)) return result;
    return lean_char_default_value();
}

/* `String.next`: the byte position after the character at `i`. */
lean_obj_res lean_string_utf8_next(b_lean_obj_arg s, b_lean_obj_arg i0) {
    if (!lean_is_scalar(i0)) return lean_nat_add(i0, lean_box(1));
    size_t i = lean_unbox(i0);
    size_t size = lean_string_size(s) - 1;
    if (i >= size) return lean_usize_to_nat(i + 1);
    return lean_box(i + rt_utf8_claims((uint8_t)lean_string_cstr(s)[i], 4));
}

lean_obj_res lean_string_utf8_next_fast_cold(size_t i, unsigned char c) {
    return lean_box(i + rt_utf8_claims(c, 4));
}

static bool starts_character(uint8_t c) {
    return (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0;
}

/* A string from bytes taken out of an existing string: characters are counted by their leading bytes. */
static lean_object * string_from_trusted(char const * bytes, size_t size) {
    size_t length = 0;
    for (size_t i = 0; i < size; i += rt_utf8_claims((uint8_t)bytes[i], 6)) length++;
    return lean_mk_string_unchecked(bytes, size, length);
}

/* `String.extract`: the bytes from position `b` up to `e`. */
lean_obj_res lean_string_utf8_extract(b_lean_obj_arg s, b_lean_obj_arg b0, b_lean_obj_arg e0) {
    size_t b = lean_is_scalar(b0) ? lean_unbox(b0) : SIZE_MAX;
    size_t e = lean_is_scalar(e0) ? lean_unbox(e0) : SIZE_MAX;
    char const * str = lean_string_cstr(s);
    size_t size = lean_string_size(s) - 1;
    if (b >= e || b >= size) return lean_mk_string_unchecked("", 0, 0);
    if (!starts_character((uint8_t)str[b])) return lean_mk_string_unchecked("", 0, 0);
    if (e > size) e = size;
    if (e < size && !starts_character((uint8_t)str[e])) e = size;
    return string_from_trusted(str + b, e - b);
}

/* ---- The rest of what compiled Lean asks of strings ---- */

/* `String.push`. Consumes `s`. */
lean_object * lean_string_push(lean_object * s, unsigned c) {
    size_t size = lean_string_size(s);
    lean_object * r;
    if (!lean_is_exclusive(s)) {
        if (lean_is_marked_linear_core(s)) rt_stop("a value marked linear was used where it would have to be copied");
        r = copy_string(s, lean_usize_mul_checked(lean_usize_add_checked(size, 5), 2));
    } else {
        r = string_with_room(s, 5);
    }
    unsigned added = put_scalar(string_bytes(r) + size - 1, c);
    lean_to_string(r)->m_size = size + added;
    lean_to_string(r)->m_length++;
    string_bytes(r)[size + added - 1] = 0;
    return r;
}

/* `String.data`: the characters as a list. Consumes `s`. Bytes that do not form a character each count as
one, the way Lean decodes. */
lean_obj_res lean_string_data(lean_obj_arg s) {
    char const * str = lean_string_cstr(s);
    size_t size = lean_string_size(s) - 1;
    lean_object * first = lean_box(0);
    lean_object * last = NULL;
    size_t i = 0;
    while (i < size) {
        uint32_t c;
        if (char_at(str, size, i, &c)) {
            i += scalar_size(c);
        } else {
            c = (uint8_t)str[i];
            i++;
        }
        lean_object * cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, lean_box_uint32(c));
        lean_ctor_set(cell, 1, lean_box(0));
        if (last == NULL) first = cell; else lean_ctor_set(last, 1, cell);
        last = cell;
    }
    lean_dec_ref(s);
    return first;
}

/* `String.toUTF8`: the bytes without the terminating zero. */
lean_obj_res lean_string_to_utf8(b_lean_obj_arg s) {
    size_t size = lean_string_size(s) - 1;
    lean_object * r = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(r), lean_string_cstr(s), size);
    return r;
}

uint64_t lean_string_hash(b_lean_obj_arg s) {
    return rt_hash_bytes((uint8_t const *)lean_string_cstr(s), lean_string_size(s) - 1, 11);
}

/* Whether `len` bytes of two strings, from the given offsets, are equal. The offsets and length come with
proofs that they are in range. */
uint8_t lean_string_memcmp(b_lean_obj_arg s1, b_lean_obj_arg s2, b_lean_obj_arg lstart, b_lean_obj_arg rstart,
                           b_lean_obj_arg len) {
    return memcmp(lean_string_cstr(s1) + lean_unbox(lstart), lean_string_cstr(s2) + lean_unbox(rstart),
                  lean_unbox(len)) == 0;
}

/* `s1 < s2`: by bytes, a prefix sorting before anything it is a prefix of. */
bool lean_string_lt(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    size_t size1 = lean_string_size(s1) - 1;
    size_t size2 = lean_string_size(s2) - 1;
    int order = memcmp(lean_string_cstr(s1), lean_string_cstr(s2), size1 < size2 ? size1 : size2);
    return order < 0 || (order == 0 && size1 < size2);
}
