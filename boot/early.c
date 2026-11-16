/*
The first C on the machine.

Called from entry.S in long mode with a stack and the first four gigabytes mapped to themselves, however the
machine was entered. Before the
program's `main` (the one Lean generates) runs, this:

  - makes the serial port usable;
  - arranges for any processor exception to be reported, on a stack of its own, and to stop the machine;
  - reads what the boot loader says about memory and devices, and keeps its own copy of the command line;
  - replaces the mapping it booted on with the real one: code that cannot be written, data that cannot be
    run, a hole under the stack, device registers, and nothing else. Address zero and everything else the
    program has no business touching is simply not there.

Nothing here interprets anything the parent instance sends. The memory map and the command line come from the
boot loader, which is on the trusted side.

Elsewhere. This is the part of Linux's start_kernel and setup_arch that a single program needs. Device
windows are announced the way Linux's drivers/virtio/virtio_mmio.c reads them from its command line
(`virtio_mmio.device=`), but here they are only noted, to be mapped and later checked against; nothing
probes or binds a driver. The real mapping is decided by a program in the small language (Mini/Map.lean); see
there for how Linux and seL4 arrange theirs.
*/
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "boot.h"

/* ---- Ports ---- */

static inline void outb(uint16_t port, uint8_t value) {
    __asm__ volatile("outb %0, %1" : : "a"(value), "Nd"(port));
}

static inline uint8_t inb(uint16_t port) {
    uint8_t value;
    __asm__ volatile("inb %1, %0" : "=a"(value) : "Nd"(port));
    return value;
}

static inline void outl(uint16_t port, uint32_t value) {
    __asm__ volatile("outl %0, %1" : : "a"(value), "Nd"(port));
}

/* ---- The serial port: the first one, as every PC-shaped machine has it ---- */

#define COM1 0x3F8

static void serial_init(void) {
    outb(COM1 + 1, 0x00);   /* no interrupts */
    outb(COM1 + 3, 0x80);   /* let the next two set the speed */
    outb(COM1 + 0, 0x01);   /* 115200 */
    outb(COM1 + 1, 0x00);
    outb(COM1 + 3, 0x03);   /* 8 bits, no parity, 1 stop bit */
    outb(COM1 + 2, 0xC7);   /* buffers on and emptied */
    outb(COM1 + 4, 0x03);   /* ready */
}

void boot_serial_write(char const * bytes, size_t length) {
    for (size_t i = 0; i < length; i++) {
        while ((inb(COM1 + 5) & 0x20) == 0) {
        }
        outb(COM1, (uint8_t)bytes[i]);
    }
}

static void print(char const * text) {
    size_t length = 0;
    while (text[length] != 0) length++;
    boot_serial_write(text, length);
}

static void print_hex(uint64_t value) {
    char digits[18] = "0x";
    for (int i = 0; i < 16; i++) digits[2 + i] = "0123456789abcdef"[(value >> (60 - 4 * i)) & 0xF];
    boot_serial_write(digits, sizeof digits);
}

/* ---- Stopping ---- */

/* An emulator started with a debug-exit device at this port ends with a status made from what is written to
it. On a machine without one the write does nothing and the processor is halted for good.

QEMU's status is twice the value written, plus one, and QEMU's status when it fails on its own account is 1.
So the value written is the code plus sixteen: no code an image stops with can be taken for QEMU failing to
start, or the other way round. scripts/run-qemu undoes this. */
#define DEBUG_EXIT_PORT 0xF4
#define DEBUG_EXIT_BASE 16

_Noreturn void boot_halt(int code) {
    if (code < 0 || code > 100) code = 100;
    outl(DEBUG_EXIT_PORT, (uint32_t)(code + DEBUG_EXIT_BASE));
    for (;;) __asm__ volatile("cli; hlt");
}

/* ---- The layout link.ld gives the image ---- */

extern char boot_text_start[], boot_text_end[];
extern char boot_rodata_start[], boot_rodata_end[];
extern char boot_data_start[], boot_data_end[];
extern char boot_stack_guard[], boot_stack_bottom[], boot_stack_top[];
extern char boot_image_end[];

static uint64_t address_of(char const * symbol) {
    return (uint64_t)(uintptr_t)symbol;
}

/* ---- Exceptions ---- */

struct fault_frame {
    uint64_t vector;
    uint64_t error;
    uint64_t rip;
    uint64_t cs;
    uint64_t rflags;
    uint64_t rsp;
    uint64_t ss;
};

_Noreturn void silo_fault(struct fault_frame const * frame) {
    uint64_t address;
    __asm__ volatile("mov %%cr2, %0" : "=r"(address));
    print("silo boot: processor exception ");
    print_hex(frame->vector);
    print(" error ");
    print_hex(frame->error);
    print(" at ");
    print_hex(frame->rip);
    print(" stack ");
    print_hex(frame->rsp);
    print("\n");
    if (frame->vector == 14) {
        /* A page fault: say what was tried, where, and why it was refused. */
        print("silo boot: ");
        print((frame->error & 0x10) != 0 ? "running" : (frame->error & 0x2) != 0 ? "writing" : "reading");
        print(" ");
        print_hex(address);
        if (address >= address_of(boot_stack_guard) && address < address_of(boot_stack_bottom))
            print(", the hole under the stack: the stack overflowed\n");
        else if ((frame->error & 0x1) == 0)
            print(", which is not mapped\n");
        else
            print(", which that memory does not allow\n");
    }
    boot_halt(3);
}

/* Exceptions are handled on a stack of their own. One that happens because the ordinary stack is gone (it
overflowed into the hole) could not be reported otherwise: the processor would fault again pushing its
state, and again, and reset. */
struct __attribute__((packed)) task_state {
    uint32_t reserved0;
    uint64_t rsp[3];
    uint64_t reserved1;
    uint64_t interrupt_stack[7];
    uint64_t reserved2;
    uint16_t reserved3;
    uint16_t io_map_base;
};

static struct task_state task_state;
static uint8_t fault_stack[64 * 1024] __attribute__((aligned(16)));
static uint64_t gdt[5];

static void segments_init(void) {
    task_state.interrupt_stack[0] = (uint64_t)(uintptr_t)(fault_stack + sizeof fault_stack);
    task_state.io_map_base = sizeof task_state;
    uint64_t base = (uint64_t)(uintptr_t)&task_state;
    uint64_t limit = sizeof task_state - 1;
    gdt[0] = 0;
    gdt[1] = 0x00AF9A000000FFFFull;   /* 0x08: 64-bit code, as entry.S had it */
    gdt[2] = 0x00CF92000000FFFFull;   /* 0x10: data */
    /* 0x18: the task state, whose descriptor takes two slots in long mode. */
    gdt[3] = (limit & 0xFFFF) | ((base & 0xFFFFFF) << 16) | (0x89ull << 40) | (((limit >> 16) & 0xF) << 48)
           | (((base >> 24) & 0xFF) << 56);
    gdt[4] = base >> 32;
    struct __attribute__((packed)) {
        uint16_t limit;
        uint64_t base;
    } pointer = { sizeof gdt - 1, (uint64_t)(uintptr_t)gdt };
    __asm__ volatile("lgdt %0" : : "m"(pointer));
    __asm__ volatile("ltr %0" : : "r"((uint16_t)0x18));
}

struct idt_entry {
    uint16_t offset_low;
    uint16_t selector;
    uint8_t stack_table;
    uint8_t kind;
    uint16_t offset_middle;
    uint32_t offset_high;
    uint32_t reserved;
};

extern void (* const boot_fault_stubs[32])(void);
static struct idt_entry idt[32];

static void faults_init(void) {
    for (int vector = 0; vector < 32; vector++) {
        uint64_t stub = (uint64_t)boot_fault_stubs[vector];
        idt[vector].offset_low = (uint16_t)stub;
        idt[vector].selector = 0x08;
        idt[vector].stack_table = 1;   /* the fault stack */
        idt[vector].kind = 0x8E;       /* present, an interrupt gate */
        idt[vector].offset_middle = (uint16_t)(stub >> 16);
        idt[vector].offset_high = (uint32_t)(stub >> 32);
        idt[vector].reserved = 0;
    }
    struct __attribute__((packed)) {
        uint16_t limit;
        uint64_t base;
    } pointer = { sizeof idt - 1, (uint64_t)(uintptr_t)idt };
    __asm__ volatile("lidt %0" : : "m"(pointer));
}

/* ---- Memory ---- */

char boot_command_line[2048];

/* What a PVH loader passes: the start-info structure of the Xen x86 HVM direct boot ABI. */
#define HVM_START_MAGIC 0x336ec578

struct hvm_start_info {
    uint32_t magic;
    uint32_t version;
    uint32_t flags;
    uint32_t nr_modules;
    uint64_t modlist_paddr;
    uint64_t cmdline_paddr;
    uint64_t rsdp_paddr;
    uint64_t memmap_paddr;     /* version 1 and later */
    uint32_t memmap_entries;
    uint32_t reserved;
};

struct hvm_memmap_entry {
    uint64_t addr;
    uint64_t size;
    uint32_t type;             /* 1 is usable memory */
    uint32_t reserved;
};

void * boot_heap_start;
size_t boot_heap_size;
void * boot_device_start;
size_t boot_device_size;

#define PAGE 0x200000ull           /* the heap is mapped in 2 MiB pages, and found in whole ones */
#define MAPPED_END 0x100000000ull  /* the page tables in entry.S reach four gigabytes */

/* How much of the memory after the image is set aside for sharing with devices. */
#define DEVICE_MEMORY PAGE

/* The usable memory after the image, in the region the image was loaded into, in whole pages: first what
is set aside for devices, then the heap. */
static void memory_init(uint64_t region_start, uint64_t region_end) {
    uint64_t start = address_of(boot_image_end);
    uint64_t end = region_end > MAPPED_END ? MAPPED_END : region_end;
    end &= ~(PAGE - 1);
    if (start < region_start || end <= start || end - start < 2 * DEVICE_MEMORY) {
        print("silo boot: no usable memory after the image\n");
        boot_halt(4);
    }
    boot_device_start = (void *)(uintptr_t)start;
    boot_device_size = (size_t)DEVICE_MEMORY;
    boot_heap_start = (void *)(uintptr_t)(start + DEVICE_MEMORY);
    boot_heap_size = (size_t)(end - start - DEVICE_MEMORY);
}

/* Both kinds of loader describe memory as a table of ranges that begin the same way: where, how much, and
what kind, 1 being usable memory. Only the distance from one entry to the next differs. */
struct __attribute__((packed)) memory_range {
    uint64_t addr;
    uint64_t size;
    uint32_t type;
};

static void memory_init_from_map(uint64_t table, uint32_t count, size_t stride) {
    uint64_t image_end = address_of(boot_image_end);
    for (uint32_t i = 0; i < count; i++) {
        struct memory_range const * range = (struct memory_range const *)(uintptr_t)(table + i * stride);
        uint64_t start = range->addr;
        uint64_t end = start + range->size;
        if (range->type == 1 && image_end >= start && image_end < end) {
            memory_init(start, end);
            return;
        }
    }
    print("silo boot: the image is not in memory the boot loader calls usable\n");
    boot_halt(4);
}

static void report_map(uint64_t table, uint32_t count, size_t stride) {
    for (uint32_t i = 0; i < count; i++) {
        struct memory_range const * range = (struct memory_range const *)(uintptr_t)(table + i * stride);
        print("silo boot: memory at ");
        print_hex(range->addr);
        print(" of ");
        print_hex(range->size);
        print(" bytes, kind ");
        print_hex(range->type);
        print("\n");
    }
}

/* What a loader passed has to be below four gigabytes, which is all that is mapped, and outside the image,
which may just have been moved onto it. */
static bool loader_data_ok(uint64_t address, uint64_t size) {
    if (address >= MAPPED_END || size > MAPPED_END - address) return false;
    return address + size <= address_of(boot_text_start) || address >= address_of(boot_image_end);
}

static void memory_init_pvh(struct hvm_start_info const * info) {
    if (!loader_data_ok((uint64_t)(uintptr_t)info, sizeof *info) || info->magic != HVM_START_MAGIC
        || info->version < 1
        || !loader_data_ok(info->memmap_paddr, (uint64_t)info->memmap_entries * sizeof(struct hvm_memmap_entry))) {
        print("silo boot: the boot loader did not pass a memory map\n");
        boot_halt(4);
    }
    memory_init_from_map(info->memmap_paddr, info->memmap_entries, sizeof(struct hvm_memmap_entry));
}

/* What a Linux boot protocol loader passes: a 4 KiB `boot_params` page. The few fields read here, by their
offsets in that page (Linux's Documentation/arch/x86/zero-page.rst and boot.rst). */
#define PARAMS_SIZE 4096
#define PARAMS_EXT_CMD_LINE 0x0c8   /* the upper half of the command line's address */
#define PARAMS_MAP_ENTRIES 0x1e8    /* one byte: how many entries the memory map has */
#define PARAMS_HEADER_MAGIC 0x202   /* "HdrS" */
#define PARAMS_CMD_LINE 0x228       /* the lower half of the command line's address */
#define PARAMS_MAP 0x2d0            /* the memory map: entries of 20 bytes, at most 128 */

static uint32_t params_u32(uint8_t const * params, size_t offset) {
    return (uint32_t)params[offset] | (uint32_t)params[offset + 1] << 8 | (uint32_t)params[offset + 2] << 16
         | (uint32_t)params[offset + 3] << 24;
}

/* Returns where the command line is, or zero for none. */
static uint64_t memory_init_linux(uint64_t info) {
    uint8_t const * params = (uint8_t const *)(uintptr_t)info;
    if (!loader_data_ok(info, PARAMS_SIZE) || params_u32(params, PARAMS_HEADER_MAGIC) != 0x53726448) {
        print("silo boot: the boot loader did not pass boot parameters\n");
        boot_halt(4);
    }
    uint32_t count = params[PARAMS_MAP_ENTRIES];
    if (count > 128) count = 128;
    memory_init_from_map(info + PARAMS_MAP, count, 20);
    uint64_t line = params_u32(params, PARAMS_CMD_LINE) | (uint64_t)params_u32(params, PARAMS_EXT_CMD_LINE) << 32;
    if (line != 0 && !loader_data_ok(line, sizeof boot_command_line)) {
        print("silo boot: the command line is somewhere it cannot be read\n");
        boot_halt(4);
    }
    return line;
}

/* ---- The command line ---- */

/* Kept in a copy of our own: the loader's is in low memory, which stops being mapped. */
static void command_line_keep(char const * line) {
    size_t i = 0;
    while (i < sizeof boot_command_line - 1 && line[i] != 0) {
        boot_command_line[i] = line[i];
        i++;
    }
    boot_command_line[i] = 0;
}

/* ---- Devices ---- */

struct boot_window boot_windows[BOOT_MAX_WINDOWS];
size_t boot_window_count;

static void window_add(uint64_t base, uint64_t size) {
    if (boot_window_count == BOOT_MAX_WINDOWS || size < 0x200 || base >= MAPPED_END || size > MAPPED_END - base) return;
    boot_windows[boot_window_count].base = base;
    boot_windows[boot_window_count].size = size;
    boot_window_count++;
}

/* A number as a kernel command line writes one: decimal, or hexadecimal after 0x. */
static bool parse_number(char const ** at, uint64_t * value) {
    char const * p = *at;
    uint64_t result = 0;
    bool any = false;
    if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) {
        p += 2;
        for (;; p++) {
            unsigned digit;
            if (*p >= '0' && *p <= '9') digit = (unsigned)(*p - '0');
            else if (*p >= 'a' && *p <= 'f') digit = (unsigned)(*p - 'a') + 10;
            else if (*p >= 'A' && *p <= 'F') digit = (unsigned)(*p - 'A') + 10;
            else break;
            result = result * 16 + digit;
            any = true;
        }
    } else {
        for (; *p >= '0' && *p <= '9'; p++) {
            result = result * 10 + (unsigned)(*p - '0');
            any = true;
        }
    }
    *at = p;
    *value = result;
    return any;
}

/* Memory-mapped virtio devices are announced the way Linux is told about them, one per
`virtio_mmio.device=<size>@<base>:<interrupt>` on the command line. The interrupt is not used. */
static void windows_from_command_line(char const * line) {
    static char const key[] = "virtio_mmio.device=";
    for (char const * p = line; *p != 0; p++) {
        if (p != line && p[-1] != ' ') continue;
        size_t matched = 0;
        while (key[matched] != 0 && p[matched] == key[matched]) matched++;
        if (key[matched] != 0) continue;
        char const * at = p + matched;
        uint64_t size, base;
        if (!parse_number(&at, &size)) continue;
        if (*at == 'K' || *at == 'k') { size *= 1024; at++; }
        else if (*at == 'M' || *at == 'm') { size *= 1024 * 1024; at++; }
        if (*at != '@') continue;
        at++;
        if (!parse_number(&at, &base)) continue;
        window_add(base, size);
    }
}

/* A loader that announces nothing may still be QEMU's microvm, which puts its eight virtio slots at fixed
addresses. Each is taken only if it answers with virtio's magic number. */
static void windows_from_microvm_slots(void) {
    for (uint64_t slot = 0; slot < 8; slot++) {
        uint64_t base = 0xfeb00000ull + slot * 0x200;
        if (*(volatile uint32_t const *)(uintptr_t)base == 0x74726976) window_add(base, 0x200);
    }
}

/* ---- The real mapping ---- */

extern uint64_t boot_pd[2048];   /* the four page directories of entry.S, one entry per 2 MiB */

/* Page tables for the 2 MiB stretches that are mapped in 4 KiB pages: the image's own, and any that holds
device registers. A machine with more of those than there are tables here is not started. */
#define TABLES 48
static uint64_t tables[TABLES][512] __attribute__((aligned(4096)));

/* What goes in the tables is decided by a program in the small language (Mini/Map.lean), printed as C when
the image is built. This only hands it the layout and makes the processor take up the result: reloading the
root makes it forget what it had cached of the old mapping. */
static void mapping_init(void) {
    uint64_t const layout[14] = {
        address_of(boot_text_start), address_of(boot_text_end),
        address_of(boot_rodata_start), address_of(boot_rodata_end),
        address_of(boot_data_start), address_of(boot_data_end),
        address_of(boot_stack_guard), address_of(boot_stack_bottom), address_of(boot_stack_top),
        address_of(boot_image_end),
        (uint64_t)(uintptr_t)boot_device_start, (uint64_t)(uintptr_t)boot_heap_start + boot_heap_size,
        (uint64_t)(uintptr_t)boot_windows, boot_window_count,
    };
    if (boot_map(layout, boot_pd, &tables[0][0], TABLES) != 0) {
        print("silo boot: more memory to map in small pages than there are tables for\n");
        boot_halt(4);
    }
    uint64_t root;
    __asm__ volatile("mov %%cr3, %0" : "=r"(root));
    __asm__ volatile("mov %0, %%cr3" : : "r"(root) : "memory");
}

/* ---- Timing that does not depend on data ---- */

/* Intel processors from Ice Lake on may take a different time over some instructions depending on the
values they work on, unless they are told not to: "data operand independent timing mode". Code that
handles a secret is written to do the same work whatever the secret is, and that is worth nothing if the
processor then takes a different time over it. So where the processor offers the mode, it is turned on, once, before
anything runs. A processor that does not offer it either predates the question or is a guest whose
hypervisor keeps the choice to itself; nothing can be done about either from here. */

#define MSR_ARCH_CAPABILITIES 0x10a
#define ARCH_CAPABILITIES_DOITM (1ull << 12)
#define MSR_UARCH_MISC_CTL 0x1b01
#define UARCH_MISC_CTL_DOITM 1ull

static uint64_t read_msr(uint32_t msr) {
    uint32_t low, high;
    __asm__ volatile("rdmsr" : "=a"(low), "=d"(high) : "c"(msr));
    return ((uint64_t)high << 32) | low;
}

static void write_msr(uint32_t msr, uint64_t value) {
    __asm__ volatile("wrmsr" : : "c"(msr), "a"((uint32_t)value), "d"((uint32_t)(value >> 32)));
}

static void cpuid(uint32_t leaf, uint32_t subleaf, uint32_t out[4]) {
    __asm__ volatile("cpuid" : "=a"(out[0]), "=b"(out[1]), "=c"(out[2]), "=d"(out[3]) : "a"(leaf), "c"(subleaf));
}

/* What became of the mode: not offered, turned on, or offered and found off again after being turned on. */
static enum { TIMING_NOT_OFFERED, TIMING_ON, TIMING_DID_NOT_STAY } timing;

static void timing_init(void) {
    uint32_t r[4];
    cpuid(0, 0, r);
    if (r[0] < 7) return;
    cpuid(7, 0, r);
    if ((r[3] & (1u << 29)) == 0) return;   /* the processor has no register that says what it offers */
    if ((read_msr(MSR_ARCH_CAPABILITIES) & ARCH_CAPABILITIES_DOITM) == 0) return;
    write_msr(MSR_UARCH_MISC_CTL, read_msr(MSR_UARCH_MISC_CTL) | UARCH_MISC_CTL_DOITM);
    timing = (read_msr(MSR_UARCH_MISC_CTL) & UARCH_MISC_CTL_DOITM) != 0 ? TIMING_ON : TIMING_DID_NOT_STAY;
}

/* ---- Saying what was found ---- */

extern uint64_t boot_loaded_at;

static bool command_line_has(char const * word) {
    for (char const * p = boot_command_line; *p != 0; p++) {
        if (p != boot_command_line && p[-1] != ' ') continue;
        size_t matched = 0;
        while (word[matched] != 0 && p[matched] == word[matched]) matched++;
        if (word[matched] == 0 && (p[matched] == 0 || p[matched] == ' ')) return true;
    }
    return false;
}

/* What the machine looks like from here, for whoever is bringing the image up somewhere new. Printed only
when the command line has the word `silo.report`. It has to happen before the real mapping is put in place,
because it reads the loader's memory map where the loader left it. */
static void report(uint64_t info, uint32_t kind) {
    print(kind == BOOT_KIND_PVH ? "silo boot: entered by a PVH loader\n"
        : kind == BOOT_KIND_LINUX32 ? "silo boot: entered by the Linux boot protocol at its 32-bit entry, loaded at "
        : "silo boot: entered by the Linux boot protocol at its 64-bit entry, loaded at ");
    if (kind != BOOT_KIND_PVH) {
        print_hex(boot_loaded_at);
        print("\n");
    }
    if (kind == BOOT_KIND_PVH) {
        struct hvm_start_info const * start = (struct hvm_start_info const *)(uintptr_t)info;
        report_map(start->memmap_paddr, start->memmap_entries, sizeof(struct hvm_memmap_entry));
    } else {
        uint8_t const * params = (uint8_t const *)(uintptr_t)info;
        uint32_t count = params[PARAMS_MAP_ENTRIES];
        report_map(info + PARAMS_MAP, count > 128 ? 128 : count, 20);
    }
    print("silo boot: heap at ");
    print_hex((uint64_t)(uintptr_t)boot_heap_start);
    print(" of ");
    print_hex(boot_heap_size);
    print(" bytes\n");
    print(timing == TIMING_ON ? "silo boot: timing that does not depend on data: turned on\n"
        : timing == TIMING_DID_NOT_STAY ? "silo boot: timing that does not depend on data: offered, but it did not stay on\n"
        : "silo boot: timing that does not depend on data: not offered by this processor\n");
    for (size_t i = 0; i < boot_window_count; i++) {
        print("silo boot: device registers at ");
        print_hex(boot_windows[i].base);
        print(" of ");
        print_hex(boot_windows[i].size);
        print(" bytes\n");
    }
}

/* ---- Handing over ---- */

int main(int argc, char ** argv);

_Noreturn void silo_boot(uint64_t info, uint32_t kind) {
    serial_init();
    segments_init();
    faults_init();
    timing_init();
    if (kind == BOOT_KIND_PVH) {
        struct hvm_start_info const * start = (struct hvm_start_info const *)(uintptr_t)info;
        memory_init_pvh(start);
        if (start->cmdline_paddr != 0 && loader_data_ok(start->cmdline_paddr, sizeof boot_command_line))
            command_line_keep((char const *)(uintptr_t)start->cmdline_paddr);
    } else if (kind == BOOT_KIND_LINUX32 || kind == BOOT_KIND_LINUX64) {
        uint64_t line = memory_init_linux(info);
        if (line != 0) command_line_keep((char const *)(uintptr_t)line);
    } else {
        print("silo boot: entered in a way this stub does not know\n");
        boot_halt(4);
    }
    windows_from_command_line(boot_command_line);
    if (boot_window_count == 0) windows_from_microvm_slots();
    if (command_line_has("silo.report")) report(info, kind);
    mapping_init();
    static char name[] = "silo";
    static char * argv[] = { name, NULL };
    boot_halt(main(1, argv));
}
