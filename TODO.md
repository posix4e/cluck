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

`Runtime/BigProofs.lean`, checked by the build, on Lean's three standard axioms.

- [x] What number a row of limbs is, and that `trim` leaves it as it was.
- [x] `add` returns the limbs of the sum; `sub` of the difference where there is one; subtraction of
      natural numbers stops at zero.
- [x] `mul` returns the limbs of the product.
- [x] `compare` says which of two numbers is larger.
- [x] One more decimal digit is times ten plus the digit.
- [x] Signed multiplication.
- [ ] Signed addition and comparison: follow from the above; not written.
- [ ] Shifts, `and`, `or`, powers.
- [ ] Division. Knuth's algorithm D; the long one.
- [ ] `Runtime/Utf8.lean` against a plain statement of UTF-8.
- [ ] That `rt/big.c` hands the arithmetic the right limbs and reads its answer rightly: that is C, and
      tested, not proved.

### The code under Lean, written in Lean

`Mini/` is a language of 64-bit words, small enough to define exactly (`Mini/Run.lean`), from which C is
printed. What is reasoned about and what is compiled are then the same text.

- [x] The language, its meaning as an interpreter that fails wherever C leaves the outcome open, and its
      printer.
- [x] The allocator in it. `rt/alloc.c` is printed, and the runtime's tests pass on it as a process, under
      the sanitizers and on bare metal. Run as the language defines it, it never reads memory nothing has
      written or steps outside an array, over a test of 300 requests and frees.
- [ ] Proofs about the allocator: that it never fails for any sequence of requests, that blocks in use
      never overlap, that a freed block is zero. Today those are tested, not proved.
- [ ] That the printer and the C compiler keep the meaning. Trusted; the printer is about 100 lines.
- [x] Giving up references and freeing (`rt/free.c`, from `Mini/Free.lean`): the same checks as the allocator's
      printed C. Not yet run as the language defines it, and nothing proved.
- [ ] Making objects permanent, and arrays (`rt/object.c`, `rt/array.c`) in it.

### Hardening the OS, before anything secret runs on it

Nothing is open here.
