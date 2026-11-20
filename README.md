# cluck

A Lean unikernel for confidential machines, with everything built on it in one repository: Lean all the way
down, with no Linux and no C library in the guest. A service on it is a function from bytes to bytes;
`Demo/` is the one that comes with it. There are three things here.

- **The OS, for AWS Nitro Enclaves.** It boots with no AWS-supplied boot files, answers its parent over
  vsock, and returns an attestation that verifies on another machine. This is where the OS started, and most
  of this file and of the other documents is about it.
- **The same OS, for Intel TDX.** It boots through x86-64 UEFI and serves the demo over a virtio Ethernet
  link, with Ethernet, IPv4, IPv6, TCP, UDP and a DNS resolver in Lean on the same minimal runtime, and
  returns a TDX report for a relying party to have quoted. See
  [building and running the TDX guest](TDX.md).
- **[`evm/`](evm/README.md), an experiment in a package of its own.** An Ethereum block importer, built from
  someone else's executable specification of the EVM in Lean, running as a service on this OS in a TDX trust
  domain. The OS does not depend on it.

The OS itself is called silo-os, and keeps that name wherever a name is part of how it works: the Lake
package is `«silo-os»`, the machine's own lines on its console begin `silo:`, and the scripts' settings begin
`SILO_`. The two targets share the runtime, its proofs and the demo service; they differ in how the machine
is entered, in what carries bytes to the service, and in what the attestation is.

A short tour of all three, with a picture of the attestation being checked in a browser, is at
<https://posix4e.github.io/cluck/> (`docs/`).

What is done and what is left is in [TODO.md](TODO.md). What it defends against, and what it does not, is in
[THREAT_MODEL.md](THREAT_MODEL.md). How to work on it is in [CONTRIBUTING.md](CONTRIBUTING.md). To build a
service of your own on it, see "Building on it" below.

Licensed under the GNU Affero General Public License, version 3 ([LICENSE](LICENSE)).

## The stack

| Layer | Language | Contents |
|---|---|---|
| Demo service | Lean | `ping`, `attest(nonce)`, `random(n)`, `selftest` |
| Drivers and kernel logic, Nitro | Lean | virtio-mmio, vsock, attestation device, serial, heartbeat, server loop |
| Network, TDX | Lean | Ethernet, ARP and neighbor discovery, IPv4, IPv6, fragments, routes, TCP, UDP, a DNS resolver (`Kernel/Net/`) |
| Minimal runtime, in Lean | Lean | big-number arithmetic and the rules of UTF-8 (`Runtime/`) |
| Minimal runtime, in a small language | programs written as data in Lean, printed as C when built | allocator, reference counting and freeing, arrays, big numbers in memory, small-number cases, hashing, strings (`Mini/`) |
| Minimal runtime, by hand | C, single-threaded | closures, making constants permanent, start-up, stopping, a few raw hardware primitives (`rt/`) |
| Boot stub, Nitro | assembly and a little C | the Linux boot protocol's header and entries, page tables, fatal-exception handlers |
| EFI entry, TDX | C | the network device, a clock and the heap as firmware provides them, and the TDX report call (`boot/efi/`) |

In the Nitro target, every byte from the parent is parsed in Lean. The C and assembly underneath never
interpret host data. In the TDX target, firmware's network driver, which is C, moves each Ethernet frame
before Lean reads it; [THREAT_MODEL.md](THREAT_MODEL.md) says what that leaves trusted.

The runtime is the part still moving out of C. About 1,470 lines of C are written by hand, 480 of them the
boot code; the rest of what compiled Lean stands on is Lean, or a program in `Mini/`. What is proved about
each, and what is only tested, is in [TODO.md](TODO.md).

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
- `Kernel/Efi.lean`: what the TDX target asks of the machine: whole Ethernet frames in and out, the device's
  address, a clock, and a TDX report. `Kernel/Net/`: the network above that. `Internet.lean` (Ethernet, ARP,
  neighbor discovery, IPv4, IPv6, ICMP echo, UDP and the framing of TCP), `Fragment.lean` (reassembly, and
  UDP too long for one frame), `Route.lean` (the next hop for a connection made from here), `Tcp.lean`,
  `Dns.lean` (a resolver), `Address.lean`. `NetInternetTest.lean`, `NetTcpTest.lean`, `NetRouteTest.lean`,
  `NetDnsTest.lean`: their tests, which run as processes.
- `TdxMain.lean`: the demo service as a whole machine on the TDX target. `DnsProbe.lean`: a machine that
  makes one DNS lookup, for trying the outbound path.
- `Ask.lean`: the parent's client, one request at a time. `Relay.lean`: reaching a service through a
  command's pipes, shared by the two.
- `verify/`: the program that decides, off the host, whether an attestation document is to be believed, the
  AWS root certificate it trusts, its test, and two documents from a real enclave. `verify-tdx-quote` is the
  same decision for a TDX quote.
- `Runtime/`: the parts of the minimal runtime that are Lean: big-number arithmetic (`Big.lean`) and the
  rules of UTF-8 (`Utf8.lean`). `Runtime/BigProofs.lean` and `Runtime/Utf8Proofs.lean`: what is proved about each.
- `Secret.lean`: `Secret.equal` and `Secret.select`, for a service that holds a secret: comparing byte
  arrays and choosing between words in time that no secret decides.
- `Mini/`: a small language for the code under Lean, written as data in Lean. `Lang.lean` is its syntax,
  `Run.lean` its meaning (an interpreter that fails wherever C leaves the outcome open), `Print.lean` its
  printer to C. The programs: `Alloc.lean` (the allocator), `Free.lean` (giving up references and freeing),
  `Number.lean` (what a big number is in memory), `Array.lean` (arrays and byte arrays), `Small.lean` (shifts,
  powers and logarithms of small numbers), `Hash.lean` (Lean's byte hash), `String.lean` (strings), `Map.lean` (the page tables put in place at boot, printed into the boot stub rather than the runtime), `Secret.lean` (comparing and choosing in time no secret decides), `Checked.lean` (sums and products of sizes that stop instead of wrapping). `Constant.lean` checks a function's text for any secret deciding its time; `WordProofs.lean` proves the arithmetic tricks. `NumberProofs.lean`: what is proved about numbers going into the arithmetic and coming out, natural numbers and integers, in a tagged word or as an object, and about operations on natural numbers from the words handed in to the word handed back. `AllocProofs.lean`: what is
  proved about the allocator. `mini-print` prints a program's C, which is not kept in the repository;
  `scripts/print-runtime` prints them all when the runtime is built. `mini-test` runs the allocator, the
  hash, strings and the mapping as the language defines them, with no C involved (`MiniStringTest.lean` plays what is
  outside the string program and checks every byte it touches).
- `fuzz/`, `MiniFuzz.lean`, `scripts/fuzz-alloc`: the allocator as its language defines it set against the
  allocator as printed and compiled, on made-up requests. This is what holds the printer and the C compiler
  to what the proofs are about.
- `Proofs.lean`: everything proved, built with the rest so that a proof that stops checking stops the build.
- `rt/`: the minimal runtime's hand-written C; `rt/bare/`: its platform with no operating system;
  `rt/hosted/`: what only the builds that run as a process use.
- `boot/efi/`: the TDX target's way in. `platform.c` is the EFI entry and what `Kernel/Efi.lean` calls,
  `mkefi.py` turns the linked image into an EFI application, and the two patches put a network driver in
  the firmware (TDVF) and make it check what the device hands back. [TDX.md](TDX.md) has the build.
- `boot/`: from the boot loader's hand-over to `main`. `linux.S` and `setup.S` are the Linux boot protocol's
  side of it; `entry.S` and `early.c` are common to every way in. `boot/tests/` holds two images that are C
  alone. `boot/README.md` is what a real enclave
  looked like from inside, and how to run one.
- `MkImage.lean`: turns a linked image into the kernel image a Linux boot protocol loader is given.
- `scripts/`: building against the runtime, measuring what it must contain, building and booting images,
  and saying what an image is made of (`image-contents`). For the TDX target: `build-efi`, `run-efi`,
  `test-efi`, `test-efi-ipv6` and `tdx-quote`.
- `third_party/eif_build/`: the versions AWS's image builder is built from in CI.
- `evm/`: the block importer, with a `lakefile.lean`, scripts and a README of its own.

## Build and test

```
lake build
.lake/build/bin/demo-test
.lake/build/bin/kernel-test
.lake/build/bin/vsock-test
.lake/build/bin/nsm-test
.lake/build/bin/driver-test
.lake/build/bin/mini-test                                    # the allocator, the hash and strings, as their language defines them
scripts/fuzz-alloc 200 400                                   # the allocator as defined against as compiled; more rounds, longer
.lake/build/bin/sim-test .lake/build/bin/demo-sim            # the service on Lean's own runtime

scripts/build-min demo-sim                                   # the same compiled Lean on the minimal runtime (prints Mini/'s C first)
.lake/build/bin/sim-test .lake/build/bin/demo-sim-min
```

`rt/README.md` has the full comparison between runtimes.

The TDX target's network, as processes, and its guest under an emulated processor (needs QEMU and OVMF);
[TDX.md](TDX.md) has the rest, and the run on Intel hardware:

```
.lake/build/bin/net-internet-test && .lake/build/bin/net-tcp-test
.lake/build/bin/net-route-test && .lake/build/bin/net-dns-test
scripts/build-efi dev && scripts/test-efi && scripts/test-efi-ipv6
```

The Nitro target on bare metal, under QEMU:

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
require «silo-os» from git "https://github.com/posix4e/cluck" @ "<commit>"
```

(`evm/` is in this repository and takes it by path instead: `require «silo-os» from ".."`.)

It imports `Kernel` and hands `Kernel.serve` a `Kernel.Service`; `OsMain.lean` is the whole of it for the
demo. The scripts find the OS's own files beside themselves, so they are run from the project's directory:

```
lake build my-service mkimage mini-print
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
| report | `05` | REPORTDATA, exactly 64 bytes | the 1024-byte TDX report |

`attest` is the Nitro target's and is refused as unavailable on the TDX target; `report` is the TDX target's
alone, and the development build of that target, which runs outside a trust domain, refuses it the same way.
