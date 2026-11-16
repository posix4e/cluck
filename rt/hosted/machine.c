/*
A machine made of ordinary memory, for running the drivers as a process.

The drivers reach hardware only through rt/bare/hw.c, which checks every address against the device windows
and the shared memory the boot stub found. This file is a boot stub that found one device window and some
shared memory, both of them plain arrays, and then is rt/bare/hw.c itself, unchanged. So a test can be the
device: whatever it writes into the registers and the queues is what the driver reads, and a driver that is
led outside what it was given stops the process the way it would stop the machine.

Used by driver-test only.
*/
#include <stdio.h>
#include <stdlib.h>

#include <lean/lean.h>

#include "../../boot/boot.h"

static uint32_t registers[0x200 / 4];
static uint8_t shared[2 << 20];

void * boot_device_start = shared;
size_t boot_device_size = sizeof shared;
struct boot_window boot_windows[BOOT_MAX_WINDOWS];
size_t boot_window_count;
char boot_command_line[2048];

_Noreturn void rt_stop(char const * why) {
    fprintf(stderr, "the machine stopped: %s\n", why);
    exit(3);
}

#include "../bare/hw.c"

/* A new machine: the registers and the shared memory as they are before anything has touched them. */
lean_obj_res silo_machine_reset(void) {
    memset(registers, 0, sizeof registers);
    memset(shared, 0, sizeof shared);
    device_used = 0;
    boot_windows[0].base = (unsigned long long)(uintptr_t)registers;
    boot_windows[0].size = sizeof registers;
    boot_window_count = 1;
    return lean_box(0);
}
