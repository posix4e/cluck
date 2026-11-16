# The minimal runtime

The C that Lean code stands on when there is no operating system: a single-threaded replacement for Lean's
own runtime, sized to what the code actually reaches. About 2,200 lines, no event loop, no threads, no C++
library, no GMP, and no C library beyond `memcpy`, `memmove`, `memset`, `memcmp` and `strlen`. It compiles
freestanding with only the compiler's own headers.

It matches `<lean/lean.h>` of Lean 4.35.0 exactly. A Lean upgrade means re-running everything below.

## What it has to provide

Compiled Lean calls its runtime through ordinary C symbols. Lean's own runtime library answers about 560 of
them. Most are never reached. `scripts/measure-runtime` relinks a program with nothing but compiled Lean on
the link line and lists the outside symbols that survive dead-code removal:

| Program | Live runtime functions |
|---|---|
| The demo service, self-test included (`demo-sim`) | 106 |
| The self-test alone (`rt-test`) | 106 |
| The big-number test (`big-test`) | 81 |
| The first service built on this, with the library it uses | 96 |
| All of them together | 108 |

Every one is defined here. The lists are in `live-symbols/` (taken on macOS arm64; Linux x86-64 gives the
same `lean_` functions). The demo's list also names the three `silo_plat_` functions it asks of its platform.

## The files

| File | What it holds |
|---|---|
| (printed) | The allocator, giving up references and freeing what the last one kept alive, and big numbers in memory. These are programs in a small language written in Lean (`Mini/Alloc.lean`, `Mini/Free.lean`, `Mini/Number.lean`); `scripts/print-runtime` prints their C when the runtime is built, and it is not kept here. |
| `object.c` | Freeing without recursion, making constants permanent, once-built constants, lazy values, mutable cells. |
| `apply.c` | Calling closures: partial, exact and over-application. |
| `array.c` | Arrays and byte arrays. |
| `string.c` | Strings and Lean's rules for UTF-8 byte positions. The rules of UTF-8 are Lean: `Runtime/Utf8.lean`. |
| `hash.c` | Lean's byte hash (MurmurHash64A), bit for bit. |
| `nat.c` | Numbers: the small cases. What a number too large for a word is in memory is `Mini/Number.lean`, printed like the allocator; its arithmetic, on 32-bit limbs, is Lean: `Runtime/Big.lean`. |
| `io.c` | Start-up and platform questions. |
| `panic.c` | Printing and stopping. |
| `hosted/platform.c` | The platform as an ordinary process: a pipe, the OS random source, `mmap`. |
| `bare/platform.c`, `bare/libc.c` | The platform with no operating system: the boot stub's serial port and memory, the processor's random numbers, and the five memory functions. |
| `bare/hw.c` | The C half of `Kernel/Hw.lean`: device registers and device memory, every address checked. |
| `hosted/alloc_checked.c` | A testing allocator: one C-library block per request, for AddressSanitizer. |

## Where it differs from Lean's runtime, on purpose

- **A Lean `panic!` stops the machine.** Lean's runtime prints and carries on with a default value.
- **A value marked linear that would have to be copied stops the machine.** Lean's runtime only does that
  when asked through an environment variable. This is what keeps a secret from being duplicated.
- **Malformed number objects, non-digit numerals and non-UTF-8 literals stop the machine** instead of being
  repaired or trusted. Compiled Lean never produces them.
- **An uncaught error from `main`** is printed in full only if it is an `IO.userError`; other kinds are named
  by number, so that Init's error formatting does not have to be kept alive.
- **Freed memory is zeroed.**
- **Big-number arithmetic is not constant-time**, same as Lean's. Secrets must not go through `Nat` or `Int`.

## How it is tested

The same compiled Lean objects are linked several ways and must agree:

```
lake build                                # against Lean's own runtime: the reference
scripts/build-min rt-test                 # against rt/
scripts/build-checked rt-test             # against rt/ under AddressSanitizer and UBSan

.lake/build/bin/rt-test | cmp - <(.lake/build/bin/rt-test-min)
.lake/build/bin/rt-test | cmp - <(ASAN_OPTIONS=detect_leaks=0 .lake/build/bin/rt-test-checked)
```

and a fourth way with no operating system at all (x86-64 Linux host):

```
scripts/build-bare rt-test
scripts/run-qemu .lake/build/bare/rt-test.elf | cmp - <(.lake/build/bin/rt-test)
```

Likewise for `big-test` (216,522 results over numbers up to 2^1024 and beyond: every pair of 66 edge
naturals and 61 edge integers, 39 hand-picked long divisions in every sign combination, and 12,000
pseudo-random rounds). `sim-test` drives the demo service linked each way, and checks the self-test digest
the service returns against the one it computes itself on Lean's runtime.

## Reproducing the measurement

```
lake build
scripts/measure-runtime demo-sim
```

