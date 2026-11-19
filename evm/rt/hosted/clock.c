/* A clock for the benchmark (Bench.lean), which runs as a process and never in an image. */
#include <lean/lean.h>
#include <time.h>

lean_obj_res evm_clock_millis(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)now.tv_sec * 1000 + (uint64_t)now.tv_nsec / 1000000));
}

lean_obj_res evm_clock_seed(void) {
    return lean_io_result_mk_ok(lean_box_uint64(1));
}
