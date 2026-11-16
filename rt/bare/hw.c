/*
The machine, as far as Lean may touch it: the C half of Kernel/Hw.lean.

Two kinds of thing can be reached from Lean, and only these:

  - device registers, inside the windows the boot stub recorded;
  - the arena of memory set aside for sharing with devices, in and out of which bytes are copied.

Every address is checked against those before it is used, and an address outside them stops the machine.
Lean never gets a pointer, so nothing a driver computes, and nothing a device reports, can be turned into a
read or write of the Lean heap, the stack or the code.

Elsewhere. In Linux a driver gets a raw pointer from ioremap() and is trusted with it. A seL4 user-level
driver can touch only the frames it holds capabilities for. Microsoft Research's Singularity gave drivers,
written in a safe language, IoMemory and IoPort objects whose every access was checked against what the
driver's manifest declared. This is that last one in miniature: the windows are the manifest, and every access
is checked against them.
*/
#include "../rt.h"

#include "../../boot/boot.h"

lean_obj_res silo_hw_windows(void) {
    lean_object * r = lean_alloc_array(2 * boot_window_count, 2 * boot_window_count);
    for (size_t i = 0; i < boot_window_count; i++) {
        lean_array_cptr(r)[2 * i] = lean_box_uint64(boot_windows[i].base);
        lean_array_cptr(r)[2 * i + 1] = lean_box_uint64(boot_windows[i].size);
    }
    return r;
}

static volatile uint32_t * register_at(uint64_t address) {
    for (size_t i = 0; i < boot_window_count; i++) {
        uint64_t base = boot_windows[i].base;
        if ((address & 3) == 0 && address >= base && address - base <= boot_windows[i].size - 4)
            return (volatile uint32_t *)(uintptr_t)address;
    }
    rt_stop("a driver reached for a register outside every device's window");
}

uint32_t silo_hw_read32(uint64_t address) {
    return *register_at(address);
}

lean_obj_res silo_hw_write32(uint64_t address, uint32_t value) {
    *register_at(address) = value;
    return lean_box(0);
}

static size_t device_used;

uint64_t silo_hw_alloc(size_t size) {
    size_t rounded = (size + 4095) & ~(size_t)4095;
    if (size == 0 || rounded < size || rounded > boot_device_size - device_used) return 0;
    uint8_t * block = (uint8_t *)boot_device_start + device_used;
    device_used += rounded;
    memset(block, 0, rounded);
    return (uint64_t)(uintptr_t)block;
}

/* Only memory that has been handed out can be read or written, not the whole arena. */
static uint8_t * device_memory(uint64_t address, size_t size) {
    uint64_t start = (uint64_t)(uintptr_t)boot_device_start;
    if (address < start || address - start > device_used || size > device_used - (address - start))
        rt_stop("a driver reached for memory outside what it shares with devices");
    return (uint8_t *)(uintptr_t)address;
}

lean_obj_res silo_hw_load(uint64_t address, size_t size) {
    uint8_t const * from = device_memory(address, size);
    lean_object * bytes = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(bytes), from, size);
    return bytes;
}

lean_obj_res silo_hw_store(uint64_t address, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    memcpy(device_memory(address, size), lean_sarray_cptr(bytes), size);
    return lean_box(0);
}

lean_obj_res silo_hw_command_line(void) {
    size_t length = strlen(boot_command_line);
    lean_object * bytes = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(bytes), boot_command_line, length);
    return bytes;
}

lean_obj_res silo_hw_pause(void) {
#if defined(__x86_64__)
    __asm__ volatile("pause");
#endif
    return lean_box(0);
}
