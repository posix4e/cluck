/* What the boot stub offers the code above it. */
#pragma once

#include <stddef.h>
#include <stdint.h>

/* How the machine was entered (entry.S records it). */
#define BOOT_KIND_PVH 1
#define BOOT_KIND_LINUX32 2   /* the Linux boot protocol's 32-bit entry */
#define BOOT_KIND_LINUX64 3   /* and its 64-bit one */

/* The serial port. */
void boot_serial_write(char const * bytes, size_t length);

/* Stops the machine. Under an emulator with a debug-exit device, the emulator ends with a status made from
`code`. */
_Noreturn void boot_halt(int code);

/* The usable memory after the image, found at boot, less what is set aside for devices. */
extern void * boot_heap_start;
extern size_t boot_heap_size;

/* Memory set aside at boot for sharing with devices: queues and their buffers. */
extern void * boot_device_start;
extern size_t boot_device_size;

/* The boot loader's command line, in a copy that stays readable. */
extern char boot_command_line[2048];

/* Where devices' registers are, as the boot loader announced them. */
struct boot_window {
    unsigned long long base;
    unsigned long long size;
};
#define BOOT_MAX_WINDOWS 32
extern struct boot_window boot_windows[BOOT_MAX_WINDOWS];
extern size_t boot_window_count;

/* The real mapping (Mini/Map.lean, printed as C when the image is built): rewrites the page directories at
`directories` from `layout`, taking 4 KiB tables from the `count` at `tables`. 0, or 1 if there were too few. */
int boot_map(uint64_t const * layout, uint64_t * directories, uint64_t * tables, size_t count);
