/*
The smallest program the boot stub can run: no Lean, no runtime. It says so over the serial port and stops.
If this prints, the machine got from the boot loader into long mode and into C with a working stack.
*/
#include "../boot.h"

int main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    static char const message[] = "silo boot: reached C in long mode\n";
    boot_serial_write(message, sizeof message - 1);
    /* Something that needs memory mapped beyond the image, the stack and a little arithmetic. */
    unsigned char * heap = boot_heap_start;
    unsigned long sum = 0;
    for (unsigned long i = 0; i < 4096 && i < boot_heap_size; i++) {
        heap[i] = (unsigned char)(i * 7);
        sum += heap[i];
    }
    static char const good[] = "silo boot: memory after the image is usable\n";
    static char const bad[] = "silo boot: memory after the image is NOT usable\n";
    if (boot_heap_size >= 4096 && sum == 522240) {
        boot_serial_write(good, sizeof good - 1);
        return 0;
    }
    boot_serial_write(bad, sizeof bad - 1);
    return 5;
}
