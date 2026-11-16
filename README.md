# silo-os

A Lean unikernel for AWS Nitro Enclaves: Lean all the way down, booting with no Linux, no C library and no
AWS-supplied boot files, answering its parent over vsock and returning an attestation that verifies on
another machine. A service on it is a function from bytes to bytes; `Demo/` is the one that comes with it.

What is done and what is left is in [TODO.md](TODO.md). What it defends against, and what it does not, is in
[THREAT_MODEL.md](THREAT_MODEL.md). How to work on it is in [CONTRIBUTING.md](CONTRIBUTING.md). To build a
service of your own on it, see "Building on it" below.

Licensed under the GNU Affero General Public License, version 3 ([LICENSE](LICENSE)).

## The stack

| Layer | Language | Contents |
|---|---|---|
| Demo service | Lean | `ping`, `attest(nonce)`, `random(n)`, `selftest` |
| Drivers and kernel logic | Lean | virtio-mmio, vsock, attestation device, serial, heartbeat, server loop |
| Minimal runtime | C, single-threaded | allocator, reference counting, closures, arrays, strings, big numbers, a few raw hardware primitives |
| Boot stub | assembly and a little C | the Linux boot protocol's header and entries, page tables, fatal-exception handlers |

Every byte from the parent is parsed in Lean. The C and assembly underneath never interpret host data.

## Layout

- `Demo/Wire.lean`: frames between parent and enclave (4-byte big-endian length, then the payload).
- `Demo/Service.lean`: the commands, as a pure decision that hands machine work back to the platform.
- `Platform.lean`: the three things the service asks of whatever is underneath it.
- `SelfTest.lean`: one pure function that exercises the runtime and returns a transcript.
- `Kernel/Vsock.lean`: the vsock stream protocol. `VsockTest.lean`: its scenarios and fuzzer.
  `Kernel/VsockProofs.lean`: the proof that its table of connections stays bounded.
- `Kernel/Nsm.lean`: what to send the Nitro Secure Module and what its answers mean. `NsmTest.lean`: its tests.
- `Kernel/Hw.lean`, `Kernel/Virtq.lean`, `Kernel/Virtio.lean`: the device layer. `Kernel/Socket.lean` and
  `Kernel/SecureModule.lean`: the two devices' drivers. `DriverTest.lean`: both against a device that lies,
  on a machine made of ordinary memory (`rt/hosted/machine.c`).
- `Kernel/CommandLine.lean`: the boot loader's command line. `KernelTest.lean`: tests of it and of the queue
  layout.
- `OsMain.lean`: the demo service as a whole machine. `ProbeMain.lean`: reports what the machine looks like
  (command line, device windows, what each device answers); the first thing to run in a real enclave.
- `DemoSim.lean`: the service over stdin and stdout. `RtTest.lean`, `BigTest.lean`: the self-test and the
  big-number test, printed.
- `DemoTest.lean`: pure tests. `SimTest.lean`: drives a running service over its pipes.
- `Kernel/Server.lean`: bringing a machine up and serving a service.
- `Ask.lean`: the parent's client, one request at a time. `Relay.lean`: reaching a service through a
  command's pipes, shared by the two.
- `verify/`: the program that decides, off the host, whether an attestation document is to be believed, the
  AWS root certificate it trusts, its test, and three documents from real enclaves.
- `Runtime/`: the parts of the minimal runtime that are Lean: big-number arithmetic and the rules of UTF-8.
  `Runtime/BigProofs.lean`: what is proved about the first.
- `Mini/`: a small language for the code under Lean, written as data in Lean: its syntax, its meaning
  (`Mini/Run.lean`), its printer to C, and the allocator written in it. `mini-print` prints the C;
  `mini-test` runs the allocator as the language defines it.
- `rt/`: the minimal runtime; `rt/bare/`: its platform with no operating system.
- `boot/`: from the boot loader's hand-over to `main`. `linux.S` and `setup.S` are the Linux boot protocol's
  side of it; `entry.S` and `early.c` are common to every way in. `boot/README.md` is what a real enclave
  looked like from inside, and how to run one.
- `MkImage.lean`: turns a linked image into the kernel image a Linux boot protocol loader is given.
- `scripts/`: building against the runtime, measuring what it must contain, building and booting images,
  and saying what an image is made of (`image-contents`).
- `third_party/eif_build/`: the versions AWS's image builder is built from in CI.

## Build and test

```
lake build
.lake/build/bin/demo-test
.lake/build/bin/kernel-test
.lake/build/bin/vsock-test
.lake/build/bin/nsm-test
.lake/build/bin/driver-test
.lake/build/bin/sim-test .lake/build/bin/demo-sim            # the service on Lean's own runtime

scripts/build-min demo-sim                                   # the same compiled Lean on the minimal runtime
.lake/build/bin/sim-test .lake/build/bin/demo-sim-min
```

`rt/README.md` has the full comparison between runtimes.

On bare metal, under QEMU:

```
scripts/build-bare hello && scripts/run-qemu .lake/build/bare/hello.bzImage       # the boot stub alone
scripts/build-bare rt-test && scripts/run-qemu .lake/build/bare/rt-test.bzImage   # Lean
scripts/check-protection bzImage                                                  # what the machine must refuse

# The service as a machine, with the host as its parent (needs /dev/vhost-vsock and socat):
scripts/build-bare silo-os
scripts/run-qemu --microvm .lake/build/bare/silo-os.bzImage 300 -device vhost-vsock-device,guest-cid=16 &
.lake/build/bin/sim-test --socket socat - VSOCK-CONNECT:16:5005
```

`scripts/build-bare` makes each image in these shapes:

- `<name>.bzImage`: a Linux kernel image, which is what a Nitro Enclave is given. It is the setup header a
  loader reads and then the image as one run of bytes, uncompressed. A loader may put it anywhere and enter
  it in 32-bit or 64-bit mode; the image moves itself to where it runs. QEMU loads it as a BIOS would and
  ends up at the 32-bit entry.
- `<name>.long.bzImage`: the same, for testing: under QEMU it is entered at the 64-bit entry instead.
- `<name>.moved.bzImage` and `<name>.onto.bzImage`: also for testing. The first moves the image to 48 MiB
  before entering it, as a loader might put it there; the second moves it on top of where it has to run,
  which it has to refuse.
- `<name>.elf`: for a PVH loader, which QEMU also is.

From the parent of a running machine or enclave, `ask` makes one request through a relay such as socat, and
`verify/verify-attestation` judges the document `attest` returns, anywhere Python and its one dependency
(`verify/requirements.txt`) are:

```
.lake/build/bin/ask selftest -- socat - VSOCK-CONNECT:16:5005
.lake/build/bin/ask attest <nonce in hex> document.bin -- socat - VSOCK-CONNECT:16:5005
verify/verify-attestation --document document.bin --nonce <the same nonce> --pcrs silo-os.pcrs.json
```

With the word `silo.report` on its command line, an image first says how it was entered, where it was
loaded, and what memory and device registers the loader told it about.

CI also rehearses a real enclave under QEMU's emulation of one (`scripts/run-qemu --enclave`), which takes a
QEMU built from source; `.github/workflows/ci.yml` has the recipe.

`scripts/build-eif <name>` packs the kernel image into the file an enclave is started from, with AWS's own
builder, and writes down the measurements such an enclave attests to.

Images are compiled and linked with the compiler and linker Lean ships. Linking Lean into one needs the
x86-64 Linux build of Lean's `Init` and `Std`: on an x86-64 Linux host that is the toolchain's own; on any
other host, unpack the Linux release of the same Lean version at `~/.elan/cross/lean-<version>-linux` (or
point `SILO_LINUX_TOOLCHAIN` at it) and the script compiles the program's modules for x86-64 itself. The
vsock test needs a Linux host, for its vsock device.

## Building on it

A project with a service of its own takes this one as a Lake dependency, pinned to a commit, since what is
pinned is part of what its image measures:

```
require «silo-os» from git "https://github.com/posix4e/silo-os" @ "<commit>"
```

It imports `Kernel` and hands `Kernel.serve` a `Kernel.Service`; `OsMain.lean` is the whole of it for the
demo. The scripts find the OS's own files beside themselves, so they are run from the project's directory:

```
lake build my-service mkimage
.lake/packages/silo-os/scripts/build-bare my-service
.lake/packages/silo-os/scripts/build-eif my-service "silo.heartbeat=3:9000"
```

An executable that is to be linked against the minimal runtime needs `rt/hosted/platform.c` among its link
objects when built as a process, as the executables in this project's `lakefile.lean` have.

## The demo protocol

A payload's first byte is the command; the rest is its body. A reply's first byte is the command with the top
bit set, or `0xFF` followed by a refusal code (`01` unknown command, `02` malformed, `03` unavailable here).

| Command | Byte | Body | Reply body |
|---|---|---|---|
| ping | `01` | anything | the same bytes |
| attest | `02` | nonce, up to 64 bytes | attestation document |
| random | `03` | count, 2 bytes big-endian, 1 to 256 | that many random bytes |
| selftest | `04` | none | digest of the runtime self-test |
