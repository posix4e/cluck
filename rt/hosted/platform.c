/*
The platform as an ordinary process.

What `Platform.lean` asks for, over a pipe and the operating system's random source, and what the minimal
runtime asks of whatever is underneath it (memory to allocate from, somewhere to print, a way to stop).
Linked into the simulator on either runtime; Lean's own runtime simply never calls the second group.
*/
#include <lean/lean.h>

#include <errno.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <unistd.h>

lean_object * lean_mk_io_user_error(lean_object * message);

static lean_obj_res failed(char const * what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

/* Platform.read: at least one byte and at most `max`, or none once standard input has ended. */
lean_obj_res silo_plat_read(size_t max) {
    if (max == 0) max = 1;
    lean_object * bytes = lean_alloc_sarray(1, 0, max);
    ssize_t got;
    do {
        got = read(STDIN_FILENO, lean_sarray_cptr(bytes), max);
    } while (got < 0 && errno == EINTR);
    if (got < 0) {
        lean_dec_ref(bytes);
        return failed("reading from the parent failed");
    }
    lean_sarray_set_size(bytes, (size_t)got);
    return lean_io_result_mk_ok(bytes);
}

/* Platform.write: every byte, however many writes that takes. */
lean_obj_res silo_plat_write(b_lean_obj_arg bytes) {
    uint8_t const * at = lean_sarray_cptr(bytes);
    size_t left = lean_sarray_size(bytes);
    while (left > 0) {
        ssize_t put = write(STDOUT_FILENO, at, left);
        if (put < 0) {
            if (errno == EINTR) continue;
            return failed("writing to the parent failed");
        }
        at += put;
        left -= (size_t)put;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Platform.random: getentropy gives at most 256 bytes a call. */
lean_obj_res silo_plat_random(size_t count) {
    lean_object * bytes = lean_alloc_sarray(1, count, count);
    uint8_t * at = lean_sarray_cptr(bytes);
    size_t left = count;
    while (left > 0) {
        size_t piece = left < 256 ? left : 256;
        if (getentropy(at, piece) != 0) {
            lean_dec_ref(bytes);
            return failed("the random source failed");
        }
        at += piece;
        left -= piece;
    }
    return lean_io_result_mk_ok(bytes);
}

/* For the minimal runtime: one region to allocate from. Reserved, not touched, so it costs nothing until used. */
void * silo_plat_heap(size_t * size) {
    size_t wanted = (size_t)1 << 30;
    void * region = mmap(NULL, wanted, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (region == MAP_FAILED) {
        *size = 0;
        return NULL;
    }
    *size = wanted;
    return region;
}

/* For the minimal runtime: diagnostics. */
void silo_plat_console(char const * bytes, size_t length) {
    while (length > 0) {
        ssize_t put = write(STDERR_FILENO, bytes, length);
        if (put <= 0) return;
        bytes += put;
        length -= (size_t)put;
    }
}

/* For the minimal runtime: stop. */
_Noreturn void silo_plat_halt(int code) {
    _exit(code);
}

/*
Kernel/Hw.lean: there are no device registers and no device memory in an ordinary process. A program that
drives hardware still links here, so that everything builds everywhere; it finds no devices, and stops if
it touches one anyway.
*/
static _Noreturn void no_hardware(void) {
    static char const message[] = "silo: this program drives hardware, and an ordinary process has none\n";
    silo_plat_console(message, sizeof message - 1);
    _exit(70);
}

lean_obj_res silo_hw_windows(void) { return lean_alloc_array(0, 0); }
uint32_t silo_hw_read32(uint64_t address) { (void)address; no_hardware(); }
lean_obj_res silo_hw_write32(uint64_t address, uint32_t value) { (void)address; (void)value; no_hardware(); }
uint64_t silo_hw_alloc(size_t size) { (void)size; no_hardware(); }
lean_obj_res silo_hw_load(uint64_t address, size_t size) { (void)address; (void)size; no_hardware(); }
lean_obj_res silo_hw_store(uint64_t address, b_lean_obj_arg bytes) { (void)address; (void)bytes; no_hardware(); }
size_t silo_hw_devices(void) { return 0; }
uint32_t silo_hw_config(size_t index, uint32_t offset, uint8_t width) { (void)index; (void)offset; (void)width; return 0xffffffff; }
uint8_t silo_hw_claim(size_t index) { (void)index; return 0; }
uint32_t silo_hw_read(uint64_t address, uint8_t width) { (void)address; (void)width; no_hardware(); }
lean_obj_res silo_hw_write(uint64_t address, uint8_t width, uint32_t value) { (void)address; (void)width; (void)value; no_hardware(); }
lean_obj_res silo_hw_load_into(uint64_t address, lean_obj_arg bytes, size_t at, size_t size) { (void)address; (void)bytes; (void)at; (void)size; no_hardware(); }
lean_obj_res silo_hw_store_from(uint64_t address, b_lean_obj_arg bytes, size_t at, size_t size) { (void)address; (void)bytes; (void)at; (void)size; no_hardware(); }
uint64_t silo_hw_ticks(void) { no_hardware(); }
lean_obj_res silo_hw_store32(uint64_t address, uint32_t value) { (void)address; (void)value; no_hardware(); }
uint16_t silo_hw_load16(uint64_t address) { (void)address; no_hardware(); }
lean_obj_res silo_hw_store16(uint64_t address, uint16_t value) { (void)address; (void)value; no_hardware(); }
lean_obj_res silo_hw_command_line(void) { return lean_alloc_sarray(1, 0, 0); }
lean_obj_res silo_hw_pause(void) { return lean_box(0); }
uint32_t silo_check(void) { no_hardware(); }
