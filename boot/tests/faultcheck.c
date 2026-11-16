/*
Does the machine refuse what it should?

Each run tries one thing that the mapping in early.c is meant to forbid, named on the command line as
`check=<name>`, and the right outcome is that it never gets to say so: the processor faults, early.c reports
what was tried and stops the machine with status 3. If the attempt goes through, this prints that it was NOT
stopped and exits 9. `check=none` tries nothing forbidden and exits 0, to show the checks are not failing for
some other reason. scripts/check-protection runs them all.

No Lean and no runtime: only the boot stub is under test.
*/
#include <stdint.h>

#include "../boot.h"
#include "../checks.c"

int main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    return boot_check();
}
