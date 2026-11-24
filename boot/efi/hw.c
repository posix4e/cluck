/*
The machine, as far as Lean may touch it, on the EFI target: the C half of Kernel/Hw.lean here, as
rt/bare/hw.c is on the other.

What can be reached is one PCI device that Lean chose and claimed, through the firmware's PCI protocol:

  - its configuration space, and that of any other device before one is claimed, as numbers read out;
  - its registers, by window (one of its six address ranges) and offset, which the firmware checks against
    the range before it touches anything;
  - an arena of memory the device may be pointed at, got from the firmware when the device is claimed, in
    and out of which bytes are copied, every address checked against what has been handed out.

Nothing here decides anything about what it reads: which device to claim, what its capabilities mean, what
a register or a ring holds, is all Lean (Kernel/Net/VirtioNet.lean). Lean never gets a pointer.

In a trust domain the firmware turns each register access into a call to the host, and gives out for the
arena pages the host can see: what is put there is the host's to read and to change at any time, and what
is copied out of it is to be treated as the host's word.
*/
#include "efi.h"
#include "../boot.h"
#include "../../rt/rt.h"

// How much memory is set aside for sharing with the device, when one is claimed.
#ifndef BOOT_DEVICE_BYTES
#define BOOT_DEVICE_BYTES (8u << 20)
#endif

static const Guid pci_guid = {0x4cf5b200, 0x68b8, 0x4ca5, {0x9e,0xec,0xb2,0x3e,0x3f,0x50,0x02,0x9a}};

static Handle *found;
static size_t found_count;
static PciIo *device;
static uint64_t window_size[6];
static uint64_t window_start[6];
static uint8_t *arena;
static size_t arena_used;

static void find(void) {
    if (found) return;
    if (efi_system_table->boot->handles(2, &pci_guid, NULL, &found_count, &found) != 0) found_count = 0;
}

size_t silo_hw_devices(void) {
    find();
    return found_count;
}

static uint32_t width_code(uint8_t width) {
    if (width == 1) return 0;
    if (width == 2) return 1;
    if (width == 4) return 2;
    rt_stop("a driver asked for a register of a width that is not one, two or four bytes");
}

uint32_t silo_hw_config(size_t index, uint32_t offset, uint8_t width) {
    find();
    PciIo *pci = NULL;
    uint32_t value = 0;
    if (index >= found_count || offset > 4096 - width) rt_stop("a driver reached past the PCI devices there are");
    if (device && found[index] == NULL) pci = device;
    else if (efi_system_table->boot->open_protocol(found[index], &pci_guid, (void **)&pci, efi_image_handle, NULL, 2) != 0 || !pci)
        return 0xffffffff;
    if (pci->config_read(pci, width_code(width), offset, 1, &value) != 0) return 0xffffffff;
    return value;
}

// The firmware's description of one address range of a device, as ACPI lays it out.
typedef struct __attribute__((packed)) {
    uint8_t tag; uint16_t length; uint8_t kind, general, specific;
    uint64_t granularity, minimum, maximum, translation, size;
} Range;

uint8_t silo_hw_claim(size_t index) {
    find();
    BootServices *bs = efi_system_table->boot;
    if (device || index >= found_count) return 0;
    Handle handle = found[index];
    // The firmware's own drivers let go of it, and it is opened so that none can take it back.
    bs->disconnect(handle, NULL, NULL);
    PciIo *pci = NULL;
    if (bs->open_protocol(handle, &pci_guid, (void **)&pci, efi_image_handle, handle, 0x10 | 0x20) != 0 || !pci) return 0;
    // Its registers answer, and it may read and write the memory it is pointed at.
    if (pci->attributes(pci, 2, 0x0200 | 0x0400, NULL) != 0) return 0;
    for (uint8_t bar = 0; bar < 6; bar++) {
        Range *range = NULL;
        window_size[bar] = 0;
        window_start[bar] = 0;
        if (pci->bar_attributes(pci, bar, NULL, (void **)&range) != 0 || !range) continue;
        if (range->tag == 0x8a && range->kind == 0) { window_size[bar] = range->size; window_start[bar] = range->minimum; }
        bs->free_pool(range);
    }
    void *host = NULL;
    size_t bytes = BOOT_DEVICE_BYTES;
    uint64_t address = 0;
    void *mapping = NULL;
    if (pci->allocate_buffer(pci, 0, 4, BOOT_DEVICE_BYTES / 4096, &host, 0) != 0 || !host) return 0;
    // Mapped as memory both sides read and write. The address the device is to use must be the one it has
    // here: Lean is told one address, not two.
    if (pci->map(pci, 2, host, &bytes, &address, &mapping) != 0 || bytes != BOOT_DEVICE_BYTES ||
        address != (uint64_t)(uintptr_t)host) return 0;
    memset(host, 0, BOOT_DEVICE_BYTES);
    arena = host;
    arena_used = 0;
    device = pci;
    found[index] = NULL;
    return 1;
}

// Window `i` is given the made-up base (i + 1) << 32, so that an address says which window it is in.
lean_obj_res silo_hw_windows(void) {
    lean_object *r = lean_alloc_array(12, 12);
    for (size_t i = 0; i < 6; i++) {
        lean_array_cptr(r)[2 * i] = lean_box_uint64((uint64_t)(i + 1) << 32);
        lean_array_cptr(r)[2 * i + 1] = lean_box_uint64(device ? window_size[i] : 0);
    }
    return r;
}

static uint8_t window_of(uint64_t address, uint8_t width) {
    uint64_t bar = (address >> 32) - 1, offset = address & 0xffffffff;
    if (!device || bar >= 6 || (offset & (width - 1)) != 0 || window_size[bar] < width || offset > window_size[bar] - width)
        rt_stop("a driver reached for a register outside every window of its device");
    return (uint8_t)bar;
}

uint32_t silo_hw_read(uint64_t address, uint8_t width) {
    uint32_t code = width_code(width), value = 0;
    uint8_t bar = window_of(address, width);
    if (device->mem_read(device, code, bar, address & 0xffffffff, 1, &value) != 0)
        rt_stop("the firmware would not read a device register");
    return value;
}

lean_obj_res silo_hw_write(uint64_t address, uint8_t width, uint32_t value) {
    uint32_t code = width_code(width);
    uint8_t bar = window_of(address, width);
    if (device->mem_write(device, code, bar, address & 0xffffffff, 1, &value) != 0)
        rt_stop("the firmware would not write a device register");
    return lean_box(0);
}

uint32_t silo_hw_read32(uint64_t address) { return silo_hw_read(address, 4); }
lean_obj_res silo_hw_write32(uint64_t address, uint32_t value) { return silo_hw_write(address, 4, value); }

uint64_t silo_hw_alloc(size_t size) {
    size_t rounded = (size + 4095) & ~(size_t)4095;
    if (!arena || size == 0 || rounded < size || rounded > BOOT_DEVICE_BYTES - arena_used) return 0;
    uint8_t *block = arena + arena_used;
    arena_used += rounded;
    return (uint64_t)(uintptr_t)block;
}

// Only memory that has been handed out can be read or written, not the whole arena.
static uint8_t *device_memory(uint64_t address, size_t size) {
    uint64_t start = (uint64_t)(uintptr_t)arena;
    if (!arena || address < start || address - start > arena_used || size > arena_used - (address - start))
        rt_stop("a driver reached for memory outside what it shares with its device");
    return (uint8_t *)(uintptr_t)address;
}

// Bytes copied by the processor's own instruction for it, which on those that have trust domains is as
// fast as anything for a frame's worth and for a megabyte. The runtime's `memcpy` (rt/bare/libc.c) is a
// loop a byte at a time, which is right for what the runtime copies and a quarter of a card driver's
// time when every frame goes through it.
static void copy(void *to, void const *from, size_t count) {
    __asm__ volatile("rep movsb" : "+D"(to), "+S"(from), "+c"(count) : : "memory");
}

lean_obj_res silo_hw_load(uint64_t address, size_t size) {
    uint8_t const *from = device_memory(address, size);
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(bytes), from, size);
    return bytes;
}

lean_obj_res silo_hw_store(uint64_t address, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    memcpy(device_memory(address, size), lean_sarray_cptr(bytes), size);
    return lean_box(0);
}

// The same into and out of a part of an array that is there already, so that a batch of frames costs no
// allocation. The array filled must have one owner: it is changed where it is.
lean_obj_res silo_hw_load_into(uint64_t address, lean_obj_arg bytes, size_t at, size_t size) {
    uint8_t const *from = device_memory(address, size);
    if (!lean_is_exclusive(bytes)) rt_stop("a driver filled an array that something else also holds");
    if (at > lean_sarray_size(bytes) || size > lean_sarray_size(bytes) - at)
        rt_stop("a driver filled an array past its end");
    copy(lean_sarray_cptr(bytes) + at, from, size);
    return bytes;
}

lean_obj_res silo_hw_store_from(uint64_t address, b_lean_obj_arg bytes, size_t at, size_t size) {
    if (at > lean_sarray_size(bytes) || size > lean_sarray_size(bytes) - at)
        rt_stop("a driver sent an array from past its end");
    copy(device_memory(address, size), lean_sarray_cptr(bytes) + at, size);
    return lean_box(0);
}

// Two bytes of device memory read, or written, in one go. A queue's position is such a pair, changed by
// the other side while this side looks: copied a byte at a time it can be read half old and half new,
// which is a position 256 away from either. (It was, until this was here: whole queues of frames were
// taken a second time, and sent a second time.) The address must be even.
static volatile uint16_t *pair_at(uint64_t address) {
    if (address & 1) rt_stop("a driver reached for two bytes of device memory at an odd address");
    return (volatile uint16_t *)device_memory(address, 2);
}

uint16_t silo_hw_load16(uint64_t address) {
    return *pair_at(address);
}

// The write is made to have happened before anything read after it: a driver writes how far it has got
// and then reads whether the other side is still looking, the other side does the same the other way
// round, and a processor that let the read go ahead of its own write would have each see the other's
// old word and both stop.
lean_obj_res silo_hw_store16(uint64_t address, uint16_t value) {
    *pair_at(address) = value;
    __sync_synchronize();
    return lean_box(0);
}

// A device register written by the processor's own store, and not by way of the firmware. In a trust
// domain the firmware does not touch a register itself: it asks the host to carry the access out. Some
// registers are the device's own all the way down and only answer to a store made on them (the
// doorbells of Google's network card, on the machines where the card is hardware): an operating system
// writes those directly, and so does this. The register must be in a window of the claimed device, like
// any other; where it is in the machine's addresses is the firmware's word.
lean_obj_res silo_hw_write_direct(uint64_t address, uint32_t value) {
    uint8_t bar = window_of(address, 4);
    if (!window_start[bar]) rt_stop("a driver wrote directly to a window the firmware gave no place for");
    *(volatile uint32_t *)(uintptr_t)(window_start[bar] + (address & 0xffffffff)) = value;
    return lean_box(0);
}

// Four bytes of device memory read in one go, at an address that is a multiple of four: a count the
// other side keeps adding to, which read a byte at a time could come out part old and part new.
uint32_t silo_hw_load32(uint64_t address) {
    if (address & 3) rt_stop("a driver reached for four bytes of device memory at an address not a multiple of four");
    return *(volatile uint32_t *)device_memory(address, 4);
}

// Four bytes of device memory written in one go, at an address that is a multiple of four: a length in
// a queue's table, say, which the other side must not see half written.
lean_obj_res silo_hw_store32(uint64_t address, uint32_t value) {
    if (address & 3) rt_stop("a driver reached for four bytes of device memory at an address not a multiple of four");
    *(volatile uint32_t *)device_memory(address, 4) = value;
    return lean_box(0);
}

lean_obj_res silo_hw_command_line(void) {
    return lean_alloc_sarray(1, 0, 0);
}

// The processor's own count of time, as it stands: for a program to see where its time goes. It is not
// a clock of anyone's (the firmware's time is `silo_efi_millis`), and in a trust domain the host cannot
// set it.
uint64_t silo_hw_ticks(void) {
    uint32_t low, high;
    __asm__ volatile("lfence; rdtsc" : "=a"(low), "=d"(high) :: "memory");
    return ((uint64_t)high << 32) | low;
}

lean_obj_res silo_hw_pause(void) {
    __asm__ volatile("pause");
    return lean_box(0);
}
