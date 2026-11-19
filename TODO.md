# To do

What is done and what is left, in the order it has to happen. "Done" means it runs and something checks it;
where that something is only an emulator, the line says so.

## The OS

Lean all the way down, booting in a Nitro Enclave with no Linux, no libc and no AWS-supplied boot files,
answering its parent over vsock and returning an attestation that verifies off-host.

**Done on 2026-11-15.** `silo-os.eif`, as CI built it, ran in a real Nitro Enclave (m5.xlarge, us-east-2,
not in debug mode). From its parent it answered the whole test conversation; its self-test digest was the
one computed on Lean's own runtime; and the attestation document it returned verified on another machine,
against the AWS root, with the nonce that was sent and the measurements CI reproduced from source. The two
documents are kept in `verify/vectors/`, and `boot/README.md` records what a real enclave looked like to
the image.

### Done

- [x] The demo service: framing and commands as pure Lean, with tests (`Demo/`, `demo-test`).
- [x] Measured what compiled Lean needs from a runtime: 108 functions for everything here and for
      the first service built on it (`scripts/measure-runtime`, `rt/live-symbols/`).
- [x] The minimal runtime (`rt/`): same output as Lean's own runtime for the self-test, the big-number test
      and the demo service, as a process on Linux and macOS, and under AddressSanitizer and UBSan. In a real
      enclave the self-test digest matched.
- [x] The boot stub (`boot/`), entered three ways. A real enclave uses the Linux boot protocol's 64-bit
      entry with the image at 1 MiB, which then moves itself to where it runs. The 32-bit entry and the PVH
      entry have only been used by QEMU. No loader has put the image anywhere but 1 MiB, so a test shape
      does: it moves itself to 48 MiB before entering, and the image finds its way home and runs the
      self-test; moved on top of where it has to go, it says so and stops.
- [x] The kernel image (`<name>.bzImage`, made by `mkimage`) and the enclave image file packed from it with
      AWS's open-source builder (`scripts/build-eif`). CI builds both twice from nothing and they agree byte
      for byte; a real enclave reported the same measurements.
- [x] Lean on bare metal: the self-test and the big-number test print over serial what they print as
      processes. Under QEMU only (a real enclave ran the self-test, not the big-number test).
- [x] The device layer in Lean: checked access to registers and device memory, virtio over memory-mapped
      registers, polled queues.
- [x] The vsock protocol in Lean, with scenarios and a fuzzer, and the socket device driver. In a real
      enclave, and under QEMU against Linux's vhost-vsock and against vhost-device-vsock.
- [x] The boot heartbeat (connect to the parent, send `0xb7`, expect it back), when the command line asks
      for it with `silo.heartbeat=CID:PORT`. `nitro-cli` accepted it from a real enclave.
- [x] The Nitro Secure Module: its messages (`Kernel/Nsm.lean`) and its driver
      (`Kernel/SecureModule.lean`). `attest` and `random` are served from the device, and random bytes
      come from it and not from the processor's generator. In a real enclave, and against the module QEMU
      emulates.
- [x] The demo service as a whole machine (`silo-os`), answering the test conversation (`sim-test`) and the
      parent's client (`ask`) from a real enclave's parent, through socat.
- [x] The off-host attestation verifier (`verify/verify-attestation`, Python: COSE signature, certificate
      chain to the AWS root, the document's shape, measurements, nonce). Tested against documents forged
      under a made-up authority and against two a real enclave returned, one of them from debug mode, which
      it refuses. It holds the chain to revocation lists it is given (`--crl`), tested on made-up lists and on
      the one AWS publishes for the first authority under its root.
- [x] The probe (`virtio-probe`): what a machine looks like from inside. Its report from a real enclave is in
      `boot/README.md`.
- [x] Memory with only the rights it needs: code not writable, data not runnable, nothing else mapped, a hole
      under the stack, exceptions on their own stack (`scripts/check-protection`). The image and device
      registers are mapped in 4 KiB pages and the registers uncached; the heap in 2 MiB pages. The checks
      themselves are run under QEMU only: they stop the machine on purpose. An image mapped this way has
      run in a real enclave (`boot/README.md`).
- [x] A rehearsal under QEMU's emulation of a Nitro Enclave, in every CI run: QEMU unpacks the EIF and boots
      it, the heartbeat goes to the parent at address 3, the service answers its test conversation, and the
      attestation document carries the measurements AWS's builder wrote down.
- [x] The socket driver and the Secure Module's against a device that lies (`driver-test`,
      `rt/hosted/machine.c`): on a machine made of ordinary memory, with the real device layer, the test
      writes what it likes into the queues and the drivers are never led outside what they were given. A device that takes nothing the driver sends leaves
      the socket stuck, and the machine stops.
- [x] The memory mapping's checks and the big-number test in a real enclave, on 2026-11-16 (an m6i.xlarge,
      debug mode, `scripts/enclave-checks`): each of the ten forbidden things was refused there as under
      QEMU, the page beside the device registers included, and the big-number test printed the 71 lines
      Lean's own runtime prints. The images are the probe, which answers the boot heartbeat first; an
      image that does not is shown nothing of.
- [x] Timing that does not depend on data: the boot stub turns the processor's mode on where it is offered.
      In a real enclave on an m6i.xlarge (Xeon Platinum 8375C) on 2026-11-16 it was offered and turned on;
      under QEMU, and on the m5 used before, it is not offered.
- [x] Proved about the vsock protocol (`Kernel/VsockProofs.lean`): no packet and no sequence of packets and
      calls makes the table of connections hold more than the endpoint allows, and a write takes no more
      than the peer has said it has room for. Not proved: that the packets a write emits carry exactly the
      bytes it says it took, and the counters once they wrap; the scenarios and the fuzzer cover those.
- [x] AWS's image builder is built in CI from source at a fixed commit, with every dependency's version fixed
      by a lock file kept here (`third_party/eif_build/`) and a fixed compiler.
- [x] Lean images build on any host, given an unpacked x86-64 Linux Lean release (`scripts/build-bare`). The
      measurements that count are those of the image built on x86-64 Linux, as CI does.

### Proofs about the runtime's Lean

`Runtime/BigProofs.lean`, checked by the build, on Lean's three standard axioms. `Runtime/Utf8Proofs.lean`,
checked by the build too, but its questions about bytes are settled by `bv_decide`: a SAT solver's answer
checked by compiled code, so those theorems also trust the compiler that ran the check.

- [x] What number a row of limbs is, and that `trim` leaves it as it was.
- [x] `add` returns the limbs of the sum; `sub` of the difference where there is one; subtraction of
      natural numbers stops at zero.
- [x] `mul` returns the limbs of the product.
- [x] `compare` says which of two numbers is larger.
- [x] One more decimal digit is times ten plus the digit.
- [x] Signed multiplication.
- [x] Signed addition and comparison, on numbers with no zero limb on top. Comparison also assumes that a
      number passed as below zero is not zero: `intCompare` would call "minus zero" less than zero.
      `Mini/Number.lean` is shown never to pass one for an integer that arrives as a tagged word (the sign
      it passes is 1 only for a number below zero), nor for one that arrives as an object of the kind this
      program makes, whose top limb is not zero. That `checked` stops on any other object is not proved.
- [x] Shifts left and right by any count a machine word holds (times and divided by that power of two,
      rounding down), `and`, `or`, and powers for any exponent a machine word holds.
- [x] Division: the quotient rounded down and the remainder, for any dividend and any divisor that is not
      zero and has no zero limb on top. By a single limb, and by two limbs or more, which is Knuth's
      algorithm D. Proved of that one: the shift sets the divisor's top bit; each guess at a quotient limb
      is never too small and at most one too large, and `refine` gets there in at most twice round, so its
      count of four is never used up; taking the guess off says rightly whether it went below zero; and
      putting the divisor back once then leaves the right remainder, the carry out of the top cancelling
      the borrow. On top of it `natDiv` (by zero gives zero), `natMod`, `intEdiv` and `intEmod` are what
      Lean's `Nat` and `Int` define. A quotient or remainder can come back with zero limbs on top, and a
      zero quotient with a minus sign; `Mini/Number.lean` takes the limbs off and makes any zero plain
      zero, which is proved (the item after the next).
- [x] `Runtime/Utf8.lean` against the standard's table (RFC 3629), stated in plain arithmetic
      (`Runtime/Utf8Proofs.lean`). `write` gives the table's bytes for every character up to U+10FFFF.
      `strict` says one, two, three or four exactly when that many bytes are there and they are the encoding
      of a character Unicode allows, so never for a surrogate, an overlong form or anything above U+10FFFF.
      Where `strict` finds a character, `read` returns the one those bytes encode and `claims` steps over
      exactly its bytes. Not stated: what `read` and `claims` answer on bytes that are not well formed, where
      they follow Lean's own runtime, which is C and has no definition here to be held against.
- [ ] That `Mini/Number.lean` hands the arithmetic the right limbs and reads its answer rightly. Proved at
      both ends of a call to the arithmetic, for numbers of every size (`Mini/NumberProofs.lean`, on Lean's
      three standard axioms), about the program as its language defines it. Not proved: an operation as a
      whole (the last paragraph here).

      A number that fits in a tagged word:
      - Going in, a natural number: `limbs_of_word`, and `nat_limbs` for one that arrives as a tagged
        word, leave in memory an array holding the limbs of that number, with no zero limb on top. They do
        nothing C leaves open and change nothing outside the room the allocator gave. All that is assumed
        of the allocator is that it returns an address.
      - Going in, an integer from -2^31 to 2^31 - 1, which arrives as a tagged word holding its 32 bits:
        `int_sign` gives 1 if it is below zero and 0 if not, and `int_limbs` leaves an array holding the
        limbs of the integer without its sign, -2^31 included, on the same terms as above.
      - `trimmed`, for any array of limbs: its loop reads only those limbs, changes nothing, and gives the
        count without the zero limbs on top.
      - Coming out, a natural number: `nat_result` and `nat_from`, where the number in the array is below
        2^63, give back the tagged word for it (twice the number, and one), whatever zero limbs the
        arithmetic left on top.
      - Coming out, an integer: `int_result`, and `int_from` on an array as the arithmetic returns one
        (limbs, then a sign), where the integer is from -2^31 to 2^31 - 1, give back the tagged word
        holding its 32 bits, whatever zero limbs were left on top. A zero with a minus sign comes back as
        plain zero. The integer `int_from` is proved to read is `signedValue`, the one
        `Runtime/BigProofs.lean` proves the arithmetic's answers about.

      A number that is an object (a header, a sign, a count and that many limbs of four bytes):
      - Going in: `checked` passes an object whose top limb is not zero and whose sign is 0 or 1, gives its
        count and changes nothing. `limbs_of_object` leaves an array holding the object's limbs. On those,
        `nat_limbs` does so for a natural number of 2^63 or more, `int_limbs` for an integer outside
        -2^31 to 2^31 - 1, and `int_sign` gives the sign the object holds.
      - Coming out: `big_new` leaves an object holding a sign and the first limbs of an array. On it,
        `nat_result` and `nat_from` for a number of 2^63 or more, and `int_result` and `int_from` for an
        integer outside -2^31 to 2^31 - 1, give back an object holding the array's limbs without the zero
        ones on top, so the same number, with a top limb that is not zero. What goes out is therefore what
        the theorems about going in assume of what comes in.
      - What these assume of the allocator, as hypotheses in each statement: the room it hands out shares
        no byte with the object or array being read, and handing it out left that object or array as it
        was. Nothing is assumed of what the room held. Also assumed: that an object's address has its
        lowest bit clear, which is how the program tells it from a tagged word, and that an array has
        fewer than 2^32 limbs. Where an array is given up at the end (`nat_from`,
        `int_from`), the object is shown right in the state `lean_dec` is handed; what `lean_dec` then
        does to memory is the allocator's and is not stated.
      - Not proved of `checked`: that it stops on an object that is not well formed. The theorems say what
        happens for an object that is.

      Not proved: an operation as a whole, such as `lean_nat_big_add`. Each calls compiled
      `Runtime/Big.lean` between the two ends, so it needs an assumption about what that call leaves in
      memory (an array holding the limbs `Runtime/Big.lean` computes, and the arguments' arrays given up),
      and the two allocator assumptions above would have to be discharged against `Mini/Alloc.lean`.

### The code under Lean, written in Lean

`Mini/` is a language of 64-bit words, small enough to define exactly (`Mini/Run.lean`), from which C is
printed. What is reasoned about and what is compiled are then the same text.

- [x] The language, its meaning as an interpreter that fails wherever C leaves the outcome open, and its
      printer.
- [x] The allocator in it. Its C is printed when the runtime is built, and the runtime's tests pass on it as a process, under
      the sanitizers and on bare metal. Run as the language defines it, it never reads memory nothing has
      written or steps outside an array, over a test of 300 requests and frees.
- [x] First proofs about the allocator, for every input (`Mini/AllocProofs.lean`): what `class_bytes` gives
      for a small class, and that a request of 1 to 4096 bytes is given a class whose block holds it with
      fewer than sixteen bytes to spare.
- [x] `rt_malloc` itself, on one path, for every state and size that meet its conditions (`malloc_fresh`): a
      request of 1 to 4096 bytes, with no freed block of its class waiting and room on the heap, does
      nothing C leaves open, returns the front of the heap past a sixteen-byte header holding its class
      and "in use", and changes nothing else.
- [x] Memory (`Mini/Memory.lean`): reading back a word just written gives the word, and a write leaves
      every read of other bytes as it was.
- [x] `rt_malloc`'s other path for a small request (`malloc_reuse`): with a freed block of its class waiting,
      whose first word is its link and whose header says it is free, it hands out that block, takes it off
      its list, clears the link, marks it in use, and changes nothing else.
- [x] `rt_free` for a block of a small class that is in use (`free_small`), for every such state: it marks
      the block free, writes zero over every byte it held (the loop, for any size: `zero_loop`), links it in
      front of its class's list, and changes nothing else.
- [x] The first of the invariant (`Mini/AllocHeap.lean`): a heap is in order when the blocks handed out so far
      lie one after another from where it began, each behind a header that says its class and state. A small
      request served from fresh heap keeps it in order with the new block added (`malloc_fresh_in_order`):
      so such a block shares no byte with any handed out before, and every earlier header is untouched.
- [x] The heap stays in order through freeing and reuse too. Writing inside a block's own bytes, marking a
      block in use or free, and zeroing it leave every header as it was (`Laid.frame_body`, `Laid.mark`,
      `Laid.zeros`); so freeing a block that was handed out (`free_small_in_order`, about the program
      itself) and handing one out again (`reuse_keeps`) keep the same blocks laid as they were.
- [x] The allocator on small blocks, for any sequence of calls (`Mini/AllocHeap.lean`). A heap is sound when
      the blocks handed out so far lie one after another, each behind a header that says its class and
      state, and every class's list is a chain of freed blocks of that class, none on it twice. Proved:
      - no two blocks that were handed out share a byte, headers included (`Laid.separate`);
      - whatever is written inside a block's own bytes, every header stays as it was (`Laid.frame_body`);
      - a heap from which nothing has been handed out is sound (`empty_sound`);
      - `rt_malloc` for 1 to 4096 bytes, from a waiting freed block or from fresh heap, and `rt_free` of a
        block that was handed out and is in use, each do nothing C leaves open and leave a sound heap sound
        (`malloc_reuse_sound`, `malloc_fresh_sound`, `free_small_sound`). These are about the program
        itself, and one call's result meets the next call's conditions.
- [ ] Still outside those theorems: blocks over 4096 bytes (the loop that finds a power of two, and their
      lists), the first call (which asks the platform for the heap), and running out of room, which stops
      the machine through a call out of the program. That a freed block is all zero is shown for the
      moment it is freed (`free_small`); it is not yet part of what "sound" says, so it is not shown to
      still hold later.
- [ ] What the caller has to keep to, and nothing here checks: that it frees only what it was handed, once.
      Freeing a block twice is caught by the header and stops the machine; freeing an address that was
      never a block is not.
- [ ] That the printer and the C compiler keep the meaning. Trusted, and now tested for the allocator:
      `scripts/fuzz-alloc` puts made-up requests (every size, frees, words written and read back, a block
      freed twice, running out) to the program as its language defines it and to the printed C compiled
      under the sanitizers, and they have to agree on every answer. Three faults put into the C on purpose
      were each caught within a few rounds. CI runs a short one. The other programs have nothing like it
      yet: freeing, numbers and arrays need objects made up for them, which is the next harness.
- [x] Giving up references and freeing (`Mini/Free.lean`): the same checks as the allocator's
      printed C. Not yet run as the language defines it, and nothing proved.
- [x] What a number too large for a word is in memory (`Mini/Number.lean`), in place of `rt/big.c`.
- [x] Arrays and byte arrays (`Mini/Array.lean`), in place of `rt/array.c`.
- [x] The small cases of shifts, powers and logarithms (`Mini/Small.lean`) and Lean's byte hash
      (`Mini/Hash.lean`), in place of `rt/nat.c` and `rt/hash.c`. The hash, run as the language defines it,
      gives what Lean's own gives.
- [x] Strings (`Mini/String.lean`), in place of `rt/string.c`. Run as the language defines it against Lean's
      own strings (`mini-test`): every operation, every byte position on and off a character, shared and
      unshared, with and without room. Any read of a byte not written, write past an object or into a
      freed one, or overlapping copy fails the run; faults put in on purpose (an off-by-one in the room
      check, a missing clamp, an over-read, a copy one byte long) were each caught. Not yet proved.
- [ ] Strings proved in bounds: every read and write inside the objects it was given or made.
- [ ] The rest of `rt/`, a file at a time: making objects permanent, start-up, stopping.
- [ ] Say where each piece of hand-written C and assembly comes from in other systems, and where it parts
      from them: the boot header and page tables (Linux's boot protocol and `head_64.S`, seL4's boot code),
      polling instead of interrupts (Solo5, DPDK), size classes (Linux's SLUB, seL4 has no kernel heap at
      all), closures (`caml_applyN` in OCaml), one address space at full privilege (MirageOS, Unikraft).
      References by file and function, never copied code.
- [x] The real mapping (`Mini/Map.lean`), in place of the page-table code in `boot/early.c`, which keeps
      only the reload of the root. `mini-test` asks it about every 2 MiB stretch of the first four
      gigabytes and every 4 KiB page of those mapped small: none is both writable and runnable, each maps to
      itself, and the code, constants, data, the stack's hole, heap and registers each get what they should.
      Faults put in on purpose (data runnable, the hole mapped, registers cached) were each caught. The whole
      `boot_map` is run only under QEMU (`scripts/check-protection`): the interpreter keeps memory as a
      chain of single-byte writes, and 3,500 words of page tables make that take minutes.
- [ ] Prove the mapping: every entry `boot_map` writes is inside the directories or the tables it was
      given, and no entry is both writable and runnable.
- [ ] Memory in the interpreter that does not slow down with every write, without changing what it means.
- [ ] A back end for the small language that writes x86-64 machine code itself, no C compiler, starting with
      the boot path (a stage0 / Forth-style bootstrap: a tiny, checkable translator instead of clang for the
      code that runs before memory protection is on). Then the translator, being small, can be checked
      against the interpreter instruction by instruction, and in time proved.
      Calling a function through its address, and floating-point bits, need the language to grow first.

### What the program's text does not say: speculation and bits that flip

The proofs are about what the program computes. They say nothing about what a processor does ahead of
knowing, or about memory that changes without being written. The parent shares the machine's cache with
the enclave, chooses every byte it parses, and may own the memory rows beside its own. One program running
one thing at a time removes the attacks that need the attacker's code inside, or something to interrupt;
it does not remove these. Four things to do about them:

- [ ] Build what we compile with the compiler's hardening against speculation: speculative-load hardening
      (a bounds check guessed wrong cannot feed a read out of bounds), retpolines, and hardening of
      straight-line speculation. The compiler Lean ships takes all of them for this target. That covers the
      C here, the C printed from `Mini/`, and the Lean modules compiled for an image. Measure what it costs
      in time and size. Lean's own `Init` and `Std` come compiled without it, about half an image; hardening
      them means building Lean's library ourselves, which is a step of its own.
- [ ] Catch corruption where it cannot be prevented. The allocator's headers hold values that are checked on
      every free and reuse. Offer the same to services: a cell that keeps a value in two forms and stops the
      machine if they disagree when it is read, for a key, a counter or a limit.
- [x] Tricks from C libraries, in the small language and proved or checked: an index past a bounds check
      masked without a branch (Linux's `array_index_nospec`, `Stmt.inBounds`, in strings and in `hw.c`);
      a compare and a select whose time no secret decides (libsodium, BearSSL: `Mini/Secret.lean`, used
      from Lean as `Secret.equal` and `Secret.select`), with a check of any function's text for the same
      (`Mini/Constant.lean`); the allocator's wipe kept from the compiler (OpenBSD's `explicit_bzero`,
      `Stmt.keep`); eight ASCII bytes at a time (glibc, musl, simdjson), reading only what belongs to the
      string; and sums and products of sizes checked in the language instead of assumed of Lean's header
      (`Mini/Checked.lean`). The arithmetic in each is proved in `Mini/WordProofs.lean`.
- [ ] Keep secrets out of reach of a guess: not beside input that is being parsed, and wiped the moment they
      are finished with. Say how in `CONTRIBUTING.md`, and make the runtime help where it can.
- [ ] Say all of this in `THREAT_MODEL.md`, which today says only that speculation is left to AWS: what the
      design removes, what the build hardens, what is caught, and what stays AWS's (the memory itself, and
      what one guest can do to another's).

### Hardening the OS, before anything secret runs on it

Nothing is open here.
