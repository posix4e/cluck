/*
The things the memory mapping in early.c is meant to forbid, each tried on request.

`boot_check` looks on the command line for `check=<name>` and tries that one thing. The right outcome is
that it never returns: the processor faults, early.c reports what was tried and stops the machine with
status 3. If the attempt goes through, it says that it was NOT stopped and returns 9. `check=none` tries
nothing forbidden and returns 0, to show the checks are not failing for some other reason.

This file is included by boot/faultcheck.c, an image that is nothing else, and by rt/bare/checks.c, which
lets a Lean image try the same things once it has done what a Nitro Enclave's parent wants first.
*/
#include <stdint.h>


static void say(char const * text) {
    size_t length = 0;
    while (text[length] != 0) length++;
    boot_serial_write(text, length);
}

static int asked(char const * name) {
    static char const key[] = "check=";
    for (char const * p = boot_command_line; *p != 0; p++) {
        size_t i = 0;
        while (key[i] != 0 && p[i] == key[i]) i++;
        if (key[i] != 0) continue;
        p += i;
        i = 0;
        while (name[i] != 0 && p[i] == name[i]) i++;
        return name[i] == 0 && (p[i] == 0 || p[i] == ' ');
    }
    return 0;
}

/* The compiler must not see through any of this: every address and every count goes through a volatile. */
static volatile uintptr_t hidden;

static void write_to(void const * where) {
    hidden = (uintptr_t)where;
    *(volatile unsigned char *)hidden = 0xC3;
}

static unsigned char read_from(uintptr_t where) {
    hidden = where;
    return *(volatile unsigned char *)hidden;
}

static void run_at(void * where) {
    hidden = (uintptr_t)where;
    *(volatile unsigned char *)hidden = 0xC3;   /* a single `ret` */
    ((void (*)(void))hidden)();
}

static char const constant[] = "a constant";
static unsigned char in_data[16] = { 1 };

static volatile unsigned long depth_limit = ~0ul;

/* Uses a good piece of stack each time round, and uses it after the call, so that this is real recursion. */
static unsigned long descend(unsigned long depth) {
    volatile unsigned char frame[4096];
    frame[0] = (unsigned char)depth;
    if (depth >= depth_limit) return frame[0];
    return descend(depth + 1) + frame[0];
}

int boot_check(void) {
    if (asked("none")) {
        /* What must work: data and the heap can be written, the stack is deep enough for ordinary use. */
        in_data[1] = 7;
        volatile unsigned char * heap = (volatile unsigned char *)boot_heap_start;
        heap[0] = heap[0];   /* written, but left as it was: a program with a heap is using it */
        depth_limit = 1000;
        say(in_data[1] == 7 && descend(0) != ~0ul ? "check: nothing forbidden was tried\n" : "check: ordinary use failed\n");
        return in_data[1] == 7 ? 0 : 9;
    }
    if (asked("write-code")) write_to((void const *)(uintptr_t)&boot_check);
    else if (asked("write-constant")) write_to(constant);
    else if (asked("run-data")) run_at(in_data);
    else if (asked("run-heap")) run_at(boot_heap_start);
    else if (asked("run-stack")) {
        unsigned char on_stack[16];
        run_at(on_stack);
    }
    else if (asked("read-zero")) hidden = read_from(16);
    else if (asked("read-low")) hidden = read_from(0x9000);
    else if (asked("overflow")) hidden = descend(0);
    else if (asked("beside-device")) {
        /* The first 4 KiB page above the registers of every device in the 2 MiB that holds the first
        device's: it is no device's, and nothing of ours is there. */
        if (boot_window_count == 0) {
            say("check: this machine announced no devices to look beside\n");
            return 8;
        }
        unsigned long long stretch = boot_windows[0].base & ~0x1fffffull;
        unsigned long long top = 0;
        for (size_t i = 0; i < boot_window_count; i++) {
            unsigned long long last = boot_windows[i].base + boot_windows[i].size - 1;
            if ((boot_windows[i].base & ~0x1fffffull) == stretch && last > top) top = last;
        }
        hidden = read_from((uintptr_t)((top & ~0xfffull) + 0x1000));
    }
    else {
        say("check: no known check named on the command line\n");
        return 8;
    }
    say("check: that was NOT stopped\n");
    return 9;
}
