/*
The memory mapping's checks (boot/checks.c), for a Lean image to try: the C half of the probe's `forbidden`.
*/
#include "../rt.h"

#include "../../boot/boot.h"
#include "../../boot/checks.c"

uint32_t silo_check(void) {
    return (uint32_t)boot_check();
}
