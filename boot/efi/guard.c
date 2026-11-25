/*
A hole under a stack, on a machine whose page tables are firmware's.

`efi_guard(start, bytes)` takes the pages from `start` for `bytes` out of the mapping, so that a stack
running down into them stops the processor at its first step there instead of writing on whatever lies
below, and has that stop said on the console and the machine halted (`silo_efi_fault`).

Two things of firmware's are changed to do it, both in memory, neither through a service of firmware's:

  Its page tables. They map memory in pages of 1 GiB, 2 MiB or 4 KiB as firmware chose. The entry for
  each page of the hole is found from the processor's root; where the page is part of a larger one,
  that one is first replaced by a table of 512 smaller ones saying exactly what it said (the tables
  are a few pages of this image's own, `spare`), and then the page's own entry is marked absent.
  Nothing else of the mapping changes. Some firmware keeps its tables read-only, which the
  processor honours only while a bit of CR0 is set; it is cleared for the writes and put back.

  Where the processor goes on a page fault and on a fault within a fault. Firmware's handlers run on
  the stack that was current, and when that stack is the thing that has run out, they cannot: the
  processor would fault again pushing what it was doing, and again, and then reset the machine with
  nothing said. So the two faults are given a stack of their own. That takes a task segment, which
  firmware's table of segments need not have: the table is copied with one added, and firmware's
  table of handlers is copied with those two entries changed. Every other exception goes where
  firmware sent it, as before.

Nothing here reads a byte that came from outside the machine. What it trusts is firmware's tables being
what the processor's manual says tables are; an entry that is not is refused, and the caller told.
*/
#include "efi.h"
#include "../boot.h"
#include "../../rt/rt.h"
#include <stdbool.h>

#define PRESENT 0x1ull
#define LARGE 0x80ull
#define FRAME 0x000ffffffffff000ull   /* where an entry points, once a large page's low bits are cleared */
#define ABOVE 0xfff0000000000000ull   /* an entry's top bits: not to be run, and the keys */

#define SPARE 8
static uint64_t spare[SPARE][512] __attribute__((aligned(4096)));
static unsigned spare_used;
static uint64_t hole_start, hole_end;

static uint64_t control(int which) {
    uint64_t value;
    if (which == 0) __asm__ volatile("mov %%cr0, %0" : "=r"(value));
    else if (which == 3) __asm__ volatile("mov %%cr3, %0" : "=r"(value));
    else __asm__ volatile("mov %%cr4, %0" : "=r"(value));
    return value;
}

/* The entry that maps the 4 KiB page at `address`, with every larger page on the way to it replaced by a
table of smaller ones that say the same. NULL if the address is not mapped, or there are no tables left. */
static uint64_t * entry_of(uint64_t address) {
    int levels = (control(4) & (1u << 12)) != 0 ? 5 : 4;
    uint64_t * table = (uint64_t *)(uintptr_t)(control(3) & FRAME);
    for (int level = levels; level > 1; level--) {
        uint64_t * entry = &table[(address >> (12 + 9 * (level - 1))) & 511];
        uint64_t was = *entry;
        if ((was & PRESENT) == 0) return NULL;
        if ((was & LARGE) == 0) {
            table = (uint64_t *)(uintptr_t)(was & FRAME);
            continue;
        }
        /* A page of 1 GiB (level 3) or 2 MiB (level 2). No other level has such pages. */
        if (level > 3 || spare_used == SPARE) return NULL;
        uint64_t size = 1ull << (12 + 9 * (level - 1)), part = size >> 9;
        uint64_t base = was & FRAME & ~(size - 1);
        /* A large page keeps one of its attribute bits at bit 12, where a 4 KiB page has part of its
        address, and a 4 KiB page keeps that bit where a large page says it is large. */
        uint64_t same = level == 3 ? (was & 0x1fff) : ((was & 0xf7f) | ((was >> 12 & 1) << 7));
        uint64_t * fresh = spare[spare_used++];
        for (unsigned i = 0; i < 512; i++) fresh[i] = (base + i * part) | same | (was & ABOVE);
        /* The table's own entry: present, with the large page's say on writing and on who may reach it;
        whether it may be run is left to the entries under it. */
        *entry = (uint64_t)(uintptr_t)fresh | (was & 0x7) | 0x20;
        table = fresh;
    }
    return &table[(address >> 12) & 511];
}

static void hex(uint64_t value) {
    char text[18] = "0x";
    for (int i = 0; i < 16; i++) text[2 + i] = "0123456789abcdef"[(value >> (60 - 4 * i)) & 15];
    rt_print_bytes(text, sizeof text);
}

/* Where the processor comes on the two faults (the stubs below), on the stack kept for them. */
__attribute__((used)) _Noreturn void silo_efi_fault(uint64_t vector, uint64_t error, uint64_t at, uint64_t stack) {
    uint64_t address;
    __asm__ volatile("mov %%cr2, %0" : "=r"(address));
    if (vector == 14 && address >= hole_start && address < hole_end) {
        rt_print("silo: the stack ran out: it reached the hole under it at ");
        hex(address);
    } else if (vector == 14) {
        rt_print((error & 0x10) != 0 ? "silo: page fault running " : (error & 0x2) != 0 ? "silo: page fault writing " : "silo: page fault reading ");
        hex(address);
    } else {
        rt_print("silo: a fault while the processor was delivering another");
    }
    rt_print(", in code at ");
    hex(at);
    rt_print(" with its stack at ");
    hex(stack);
    rt_print("\n");
    boot_halt(3);
}

/* The processor has pushed the error's code, then where it was: the instruction at 8, the stack at 32. */
__attribute__((naked)) static void on_page_fault(void) {
    __asm__("mov $14, %edi\n\tmov (%rsp), %rsi\n\tmov 8(%rsp), %rdx\n\tmov 32(%rsp), %rcx\n\tcall silo_efi_fault");
}
__attribute__((naked)) static void on_double_fault(void) {
    __asm__("mov $8, %edi\n\tmov (%rsp), %rsi\n\tmov 8(%rsp), %rdx\n\tmov 32(%rsp), %rcx\n\tcall silo_efi_fault");
}

struct __attribute__((packed)) pointer {
    uint16_t limit;
    uint64_t base;
};
struct gate {
    uint16_t offset_low, selector;
    uint8_t stack_table, kind;
    uint16_t offset_middle;
    uint32_t offset_high, reserved;
};
static struct __attribute__((packed)) {
    uint32_t reserved0;
    uint64_t rings[3], reserved1, stacks[7], reserved2;
    uint16_t reserved3, ports;
} task;
static uint64_t segments[128];
static struct gate gates[256];
static _Alignas(16) uint8_t fault_stack[64 * 1024];

static void set_gate(int vector, void (*to)(void), uint16_t code) {
    uint64_t address = (uint64_t)(uintptr_t)to;
    gates[vector] = (struct gate){ (uint16_t)address, code, 1, 0x8e, (uint16_t)(address >> 16), (uint32_t)(address >> 32), 0 };
}

/* False if firmware's tables are not of a size that can be copied here; nothing is changed then. */
static bool faults_on_their_own_stack(void) {
    struct pointer had_segments, had_gates;
    __asm__ volatile("sgdt %0" : "=m"(had_segments));
    __asm__ volatile("sidt %0" : "=m"(had_gates));
    size_t segment_bytes = (size_t)had_segments.limit + 1, gate_bytes = (size_t)had_gates.limit + 1;
    if (segment_bytes % 8 != 0 || segment_bytes + 16 > sizeof segments || gate_bytes > sizeof gates || gate_bytes < 15 * sizeof gates[0])
        return false;
    memcpy(segments, (void *)(uintptr_t)had_segments.base, segment_bytes);
    memcpy(gates, (void *)(uintptr_t)had_gates.base, gate_bytes);
    /* The task segment: all it is for is the first of its seven stacks. */
    task.stacks[0] = (uint64_t)(uintptr_t)(fault_stack + sizeof fault_stack);
    task.ports = sizeof task;
    uint64_t base = (uint64_t)(uintptr_t)&task, limit = sizeof task - 1;
    size_t index = segment_bytes / 8;
    segments[index] = (limit & 0xffff) | ((base & 0xffffff) << 16) | (0x89ull << 40) | ((base >> 24 & 0xff) << 56);
    segments[index + 1] = base >> 32;
    uint16_t code;
    __asm__ volatile("mov %%cs, %0" : "=r"(code));
    set_gate(8, on_double_fault, code);
    set_gate(14, on_page_fault, code);
    struct pointer now_segments = { (uint16_t)(segment_bytes + 16 - 1), (uint64_t)(uintptr_t)segments };
    struct pointer now_gates = { (uint16_t)(gate_bytes - 1), (uint64_t)(uintptr_t)gates };
    __asm__ volatile("lgdt %0" : : "m"(now_segments));
    __asm__ volatile("ltr %0" : : "r"((uint16_t)(index * 8)));
    __asm__ volatile("lidt %0" : : "m"(now_gates));
    return true;
}

/* True when every page from `start` for `bytes` is out of the mapping and the two faults have their
stack. `start` and `bytes` are whole pages. False, with what was wrong said, when it could not be done: the
pages whose entries were reached before that are out all the same. */
bool efi_guard(void * start, size_t bytes) {
    uint64_t from = (uint64_t)(uintptr_t)start;
    if ((from & 4095) != 0 || (bytes & 4095) != 0 || bytes == 0) {
        rt_print("silo: a hole under the stack has to be whole pages\n");
        return false;
    }
    if (!faults_on_their_own_stack()) {
        rt_print("silo: firmware's tables of segments and of handlers are not of a size to copy\n");
        return false;
    }
    uint64_t protect = control(0);
    __asm__ volatile("mov %0, %%cr0" : : "r"(protect & ~(1ull << 16)));
    bool done = true;
    for (uint64_t page = from; page < from + bytes; page += 4096) {
        uint64_t * entry = entry_of(page);
        if (entry == NULL) { done = false; break; }
        *entry &= ~PRESENT;
        __asm__ volatile("invlpg (%0)" : : "r"(page) : "memory");
    }
    __asm__ volatile("mov %0, %%cr0" : : "r"(protect));
    if (!done) {
        rt_print("silo: firmware's page tables did not let a hole be made under the stack\n");
        return false;
    }
    hole_start = from;
    hole_end = from + bytes;
    return true;
}
