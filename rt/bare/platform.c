/*
The platform on bare metal, so far.

What the minimal runtime asks of whatever is underneath it (memory, somewhere to print, a way to stop), from
the boot stub, and what `Platform.lean` asks for, as far as it exists without a socket driver: writing goes
to the serial port, there is nothing to read, and random bytes come from the processor.

This is enough to run a program that only prints. The vsock driver replaces the reading and writing.
*/
#include <lean/lean.h>

#include "../../boot/boot.h"

lean_object * lean_mk_io_user_error(lean_object * message);

static lean_obj_res failed(char const * what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

void * silo_plat_heap(size_t * size) {
    *size = boot_heap_size;
    return boot_heap_start;
}

void silo_plat_console(char const * bytes, size_t length) {
    boot_serial_write(bytes, length);
}

_Noreturn void silo_plat_halt(int code) {
    boot_halt(code);
}

/* Platform.read: nobody is on the other end yet. */
lean_obj_res silo_plat_read(size_t max) {
    (void)max;
    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
}

/* Platform.write: to the serial port. */
lean_obj_res silo_plat_write(b_lean_obj_arg bytes) {
    boot_serial_write((char const *)lean_sarray_cptr(bytes), lean_sarray_size(bytes));
    return lean_io_result_mk_ok(lean_box(0));
}

/* Whether the processor has RDRAND: CPUID leaf 1, ECX bit 30. */
static bool has_rdrand(void) {
    uint32_t eax = 1, ebx, ecx = 0, edx;
    __asm__ volatile("cpuid" : "+a"(eax), "=b"(ebx), "+c"(ecx), "=d"(edx));
    (void)ebx;
    (void)edx;
    return (ecx & (1u << 30)) != 0;
}

/* Platform.random: from the processor's generator. It can fail to have a number ready; it is asked a few
times before that counts as a failure. In an enclave the Nitro Secure Module's generator takes this over. */
lean_obj_res silo_plat_random(size_t count) {
    if (!has_rdrand()) return failed("this processor has no random number generator");
    lean_object * bytes = lean_alloc_sarray(1, count, count);
    uint8_t * at = lean_sarray_cptr(bytes);
    size_t done = 0;
    while (done < count) {
        uint64_t word = 0;
        bool ok = false;
        for (int attempt = 0; attempt < 16 && !ok; attempt++) {
            unsigned char carry;
            __asm__ volatile("rdrand %0; setc %1" : "=r"(word), "=qm"(carry));
            ok = carry != 0;
        }
        if (!ok) {
            lean_dec_ref(bytes);
            return failed("the processor's random number generator gave nothing");
        }
        for (int i = 0; i < 8 && done < count; i++) at[done++] = (uint8_t)(word >> (8 * i));
    }
    return lean_io_result_mk_ok(bytes);
}
