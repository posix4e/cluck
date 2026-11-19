# Threat model

What silo-os is defending, from whom, with what, and where it does not yet. The OS exists to run services
that hold secrets beside a machine assumed hostile. What a particular service adds to this is for that
service's own threat model.

Each defence below is marked **built**, **partly** or **not built**. A defence that is not built is not a
defence yet.

## Intel TDX Ethernet target

This target runs as a single x86-64 EFI application inside a trust domain. The following
Nitro-specific claims about isolation, vsock, PCRs, page tables and the Secure Module apply to
the Nitro target. The TDX target depends on Intel's hardware, TDX module, TDVF and its boot
services, including its PCI, FAT and virtio drivers. Firmware owns the page tables, exceptions,
device-facing memory and network queues for the lifetime of the application. The patched network driver checks completion counts, lengths and descriptor
IDs at runtime and selects DMA buffers from driver-owned records. Its code processes
I/O below the Lean Ethernet parser. The Nitro boot stub's W^X and stack-guard checks do not
exercise this path.

The host and anyone on the network can observe, change, replay or drop Ethernet traffic.
ARP and Neighbor Discovery establish reachability. Neither authenticates a peer. The demo
serves cleartext TCP and UDP, and exposes its framing and transport state to remote clients.
The guest bounds TCP connections, buffered stream data, fragment assemblies and their lifetimes.
An attacker can still occupy those limits, withhold acknowledgments, exhaust CPU time or
prevent the firmware or virtual NIC from making progress. No secret should be exchanged on
the strength of a TCP connection or checksum.

The EFI image and its firmware are separate inputs to measurement. A TDREPORT binds the 64
caller-supplied REPORTDATA bytes to the local TD. The host-side QGS helper transports it to
Intel's quoting service and returns the quote bytes. A relying party must verify the signature
and collateral, freshness, REPORTDATA, DEBUG attribute, expected MRTD and relevant RTMRs
(including the measured boot of the expected EFI application) under its own policy. The
launcher does not establish a verifier policy or bind a session key to the demo connection.
A file hash of the EFI application alone is insufficient to establish the trust domain's
identity. The development EFI image supplies no TDX evidence.

## The EVM service (`evm/`)

`evm/` builds an image of its own: the TDX Ethernet target above with the demo replaced by an Ethereum block
importer. It is an experiment, and it breaks rules the OS holds itself to. Everything said of the TDX
target applies to it; this is what it adds.

**Someone else's code is in the image.** The service is Jaune, an executable specification of the EVM that
this project did not write and has not reviewed: the interpreter, the block and transaction rules, RLP, the
state trie, and Keccak, SHA-256, RIPEMD-160, BLAKE2, secp256k1, P-256, bn254, BLS12-381 and KZG, all in Lean.
With it come a handful of compiled functions from Lean's library and from mathlib's dependencies, which the
linker takes because Jaune's compiled code calls them. Jaune is not what a node beside the guest would run,
so "one flaw is not enough" is not obviously lost, but nothing here has been checked against that section.

**Start-up routines that do nothing.** `evm/rt/start.c` stands in for seven of mathlib's. If any code the
service reaches reads a constant one of them would have built, it reads memory nothing has written. This is
the rule "nothing that is not there may pass for something that is" broken on purpose, and the fixtures
agreeing is all that stands behind it.

**A stack with no guard.** `evm/boot/stack.c` moves `main` to 64 MiB of the image's own memory. Recursion
past the end of it writes into the image. How deep Jaune recurses depends on the request, and no bound on
that depth has been worked out.

**The input.** Anyone who can reach TCP port 5005 can send a request of up to 8 MiB. `Evm/Service.lean`
reads it in Lean, with every length checked against what is left of the request; Jaune's own decoder then
reads the blocks. The C added here never looks at a byte of it: `evm/rt/names.c` passes numbers through to
Lean, and the other two files hold no data at all.

**Time and memory.** A block's cost is not bounded by its gas: one fixture takes 39 seconds for 4.5M gas.
The machine reads no packet while an import runs, so one request holds off every other client for as long
as it takes, and a sender who wants that can have it. Jaune holds byte strings as lists, many bytes of heap
for each byte of input, on a heap of 256 MiB; a request that needs more stops the machine, which says so.

**The answer proves nothing yet.** It comes back over cleartext TCP from a machine that has shown no
evidence of what it is. The guest can produce a TDREPORT, but this service does not carry that command, and
nothing binds a report to a request and its response. Until something does, a response is worth what the
network between is worth.

**No secret is held.** The service has no key. Its arithmetic is on `Nat` throughout and takes time that
depends on the values, which is the reason a service with a key could not be built on Jaune as it is.

## What is being protected

| Asset | When | Why it matters |
|---|---|---|
| The integrity of the code that runs in the enclave | Now | An attestation says "this measured image is running". That is only worth something if bytes from outside cannot make the image do anything its source does not say. |
| What a service keeps in memory: keys, counters, decisions | When a service has any | The OS has to hand a service a machine on which its secrets and its state are its own. The demo service here holds none. |

The OS is held to the standard a service with a key needs, because such a service runs on it unchanged.

## Who is trusted

- **AWS's hypervisor and the Nitro Secure Module.** They load the image, isolate its memory, emulate its two
  devices and sign its attestation. Nothing here defends against AWS.
- **The processor.**
- **The boot loader's hand-over**: where it puts the image, and the memory map and the command line (which
  says where devices are, and whom to send the boot heartbeat to) that it passes. They come from the
  hypervisor. The C that reads them checks only that they are where it can read and not under the image.
- **The tools that build the image**: the Lean compiler, the C compiler and linker Lean ships, and Lean's own
  compiled `Init` and `Std`, which are linked in as released, unreviewed by us.
- **The code in this repository.**

## Who is not

**The parent instance: completely.** Assume an attacker with root on it. They:

- choose every byte the enclave receives, in whatever pieces and order they like;
- decide whether and when packets arrive, and can open and abandon connections at will;
- can start, stop and restart the enclave, and run as many copies as they please;
- share the physical machine and its last-level cache with the enclave;
- can time every reply as precisely as the machine allows, as often as they want;
- see everything the enclave prints if it was started in debug mode.

**Anyone further away** (the network, the operator's other systems) reaches the enclave only through the
parent, so is covered by the above.

## One flaw is not enough

The aim of the design: a flaw that breaks the parent does not also break the enclave, and the other way
round. A service can then be one of two parties that must both agree, with the other on the parent, and
taking both takes two flaws in two bodies of code that share none.

Why the two flaws cannot be the same one: no code runs on both sides.

- **The parent** runs a general-purpose stack, all of it stock: the Linux kernel, a C library, its
  applications and their cryptography, and whatever else the operator installs.
- **The enclave** runs none of that. It has no Linux, no C library, and no cryptography or parser written in
  C. Its whole content is this repository (Lean, a runtime under it that is partly Lean, partly programs
  printed as C, and about 1,000 lines of C by hand, and a boot stub), Lean's own `Init` and `Std`, and
  whatever the service brings.

A Nitro Enclave is usually a Linux kernel, an init, AWS's libraries and an application in a container, which
puts the same kernel, the same C library and often the same cryptography on both sides of the vsock: one
flaw in any of them is a flaw in both. That is the reason the enclave here is written from nothing, and the
reason its dependencies are kept few. Each one added is one more thing whose flaw is the enclave's.

A deployment keeps to this only if the parent runs stock software and nothing from this repository. `ask`
is the exception here: it speaks the demo service's framing, which the enclave also contains, and is built
with the same Lean. It is for testing, holds no key, and is not part of a deployment.

Where one flaw would still be enough, because it lies under both sides:

- **AWS's hypervisor and the Secure Module.** Both the parent and the enclave are its guests.
- **The processor.**
- **One hand on both sides' software.** If the same pipeline, credentials or person can replace the parent's
  software and the enclave image, that is one thing to compromise, not two. A replaced enclave
  image changes its measurements, which the verifier catches, provided whoever verifies is not also the one
  who was compromised.

## What the attacker can try, and what stands in the way

### Hostile bytes over vsock

The only input. The aim would be memory corruption: turn an attested image into the attacker's code.

- **Built:** every byte from the parent is parsed in Lean, which checks every index. The C and assembly
  underneath never interpret host data.
- **Built:** a malformed packet is dropped, a packet for no connection is reset, a protocol violation ends
  that connection, the connection table is bounded, and a frame's size is decided from its header before any
  of it is buffered. The protocol is fuzzed, and the bound on the table is proved for every sequence of
  packets and calls (`Kernel.Vsock.bounded_always`).
- **Built:** drivers cannot reach arbitrary memory. Lean may touch only device registers inside announced
  windows and a dedicated arena of device memory, by copy; any other address stops the machine
  (`Kernel/Hw.lean`, `rt/bare/hw.c`).
- **Partly:** the runtime under Lean. All of it is held to Lean's own runtime by differential tests and run
  under AddressSanitizer and UBSan, which is evidence, not proof. A bug in it reachable from Lean code is a
  memory-safety bug in the enclave. It is in three kinds, with different things standing behind each:
  - Lean (`Runtime/`): big-number arithmetic and the rules of UTF-8. Every index is checked by the
    language. Sums, differences, products and comparison are proved to be what they should; division,
    shifts and UTF-8 are not yet.
  - Programs in a small language (`Mini/`), printed as C: the allocator, freeing, arrays, big numbers in
    memory, hashing, strings. The language has a definition that fails wherever C leaves the outcome open. Against
    it the allocator is proved, for blocks up to 4096 bytes and any sequence of requests and frees: no two
    blocks share a byte, and a caller writing inside its block cannot damage a header. Large blocks, and
    the other programs, are tested; strings are also run as the language defines them against Lean's own, where reading a byte not written, or writing past an object or into a freed one, fails the run. The printer, about 150 lines, and the C
    compiler are trusted to keep the meaning; nothing checks that they do but the tests.
  - C by hand (`rt/`), about 520 lines that reach an image: closures, making constants permanent,
    start-up, stopping, device access. Tested only.
- **Built:** memory has only the rights it needs. Code cannot be written; constants, data, the heap and the
  stack cannot be run; address zero and everything else the program does not use is not mapped at all; and
  there is a hole under the stack, so a stack that overflows stops the machine instead of walking into the
  data below it. The image and device registers are mapped in 4 KiB pages, so each piece of the image has
  its own rights to the page and the memory beside a device's registers is not there; the registers are
  mapped uncached. Exceptions are reported on a stack of their own. `scripts/check-protection` boots the
  machine once per forbidden thing and requires each to be refused. What goes in the page tables is decided by a
  program in the small language (`Mini/Map.lean`), and every entry it decides is checked as the language
  defines it: none both writable and runnable, each mapping a page to itself. The same ten checks have been refused
  in a real enclave (`scripts/enclave-checks`).
- **Not addressed:** that closes off injecting code, not reusing the code that is there. Everything runs in
  one address space at the processor's highest privilege, at fixed addresses, so a memory-safety bug in the
  runtime could still be steered through existing code. The defence against that is not having the bug.

### Denial of service

The parent can always stop the enclave or never deliver a packet. Availability against the parent is not a
goal. What matters is that exhaustion fails closed:

- **Built:** running out of memory, overflowing the stack, a failed assertion, a Lean `panic!`, or a driver
  touching a bad address stops the machine. Nothing carries on in a state its authors called impossible.
- **Built:** every wait on a device is bounded, and running out of patience is a refusal or a stop, never a
  quiet carrying on. A Secure Module that does not answer means the request that needed it is refused (no
  random bytes, no time, no attestation). A socket device that does not take a packet stops the machine:
  its one transmit buffer may still be the device's, and there is nobody left to serve. Memory shared with
  devices is handed out only while the machine comes up, so running out of it means a device is not started
  and the machine stops there. None of this costs anything the parent could not already take by stopping
  the enclave. A service that holds a key loses it with the machine and has to be designed for that.

### Rollback and cloning

Run an old copy of the enclave's state, or many copies, so that each has a fresh allowance.

- **Built, by having nothing to roll back:** the OS keeps no state outside memory and seals nothing.
- **By design:** a service has nowhere to keep state across a restart. One that needs to count something
  for its whole life has to make its life the machine's: a key made at boot that never leaves memory, and
  counters beside it.

### Timing and cache side channels

The attacker shares the host, requests work at will and times it.

- **Built:** freed memory is zeroed, and the zeroing is kept: the compiler is told the block may be read
  afterwards, so it cannot drop the stores as dead (what `explicit_bzero` is for). No interrupts are ever
  enabled, so no secret is spilled by one.
- **Partly:** code that handles a service's secrets in time that does not depend on them. The OS gives two
  pieces, `Secret.equal` (byte arrays compared without stopping at the first difference) and `Secret.select`
  (a choice without a branch), written in the small language and checked (`Mini/Constant.lean`) to let no
  secret decide a branch, a loop, an address or a division. The rest is the service's to bring. Lean's
  natural numbers are not such code: their arithmetic depends on their size, so a secret must never become
  one; nor are `==` on strings and byte arrays, which stop at the first difference.
- **Built, where the processor offers it:** the boot stub turns on the processor's mode in which the time an
  instruction takes does not depend on the values it works on (Intel's, from Ice Lake on), before anything
  else runs, and says in its report whether it could. A Nitro Enclave is offered the mode on a processor
  that has it: on an m6i.xlarge the report said it was turned on. The processor QEMU emulates does not
  offer it, nor does the older one in an m5, where the question does not arise.
- **Partly:** speculative execution. Where the runtime reads at an index it has just checked (strings, device
  registers, memory shared with devices), the index is masked without a branch first, so a check the
  processor guesses wrong still reads in bounds (Linux's `array_index_nospec`; the mask is proved in
  `Mini/WordProofs.lean`). The bounds checks compiled Lean makes itself, in Lean's header and in `Init` and
  `Std`, are not masked; building with the compiler's speculative-load hardening is the next step (TODO.md).
- **Not addressed:** power and frequency channels. For those the enclave relies on what AWS does.

### A device that lies

The hypervisor is trusted, so this is defence in depth, not a boundary.

- **Built:** what a device reports is still treated as a number to check: a queue size is clamped, a length
  it says it wrote is cut to the buffer, an index is only used modulo the queue size, and the Secure Module's
  answers are read strictly (exactly the documented shape, nothing extra, nothing left over).
- **Built:** the socket driver and the Secure Module's are run against a device that lies (`driver-test`). The machine is ordinary
  memory with the real device layer on top, and the test writes into the queues what a device would: entries
  naming buffers that do not exist, lengths no buffer has, indices that jump, noise, and packets that are
  nearly right. The driver is never led outside what it was given, hands up nothing longer than a buffer,
  and keeps its table of connections within its bound. With the driver's two checks on a length taken out,
  the test stops at once. The Secure Module is given proper answers, proper ones cut short and noise, with
  whatever it likes said about which buffer was used and how much was written; its driver answers or
  refuses, and gives exactly as many random bytes as were asked for or none.

### A different image than the one reviewed

- **Built:** the enclave image and its measurements are built by CI, twice from nothing, and must agree
  byte for byte. A real enclave started from that image attested to the same measurements, and QEMU's
  emulation, reading the same file, arrives at them too.
- **Built:** the verifier (`verify/verify-attestation`). It is outside the enclave but it is what an operator
  trusts before sending funds, so it is part of the trusted base, along with Python and the one library it
  uses for certificates and signatures. It accepts a document only if it is signed by a chain to the AWS
  root (pinned by the fingerprint AWS publishes), carries the nonce the verifier sent, and has the
  measurements of the image built from source. It refuses the all-zero measurements of an enclave started in
  debug mode. It is tested against forged documents and against two from a real enclave.
- **Built, as far as AWS publishes:** the verifier holds the chain to certificate revocation lists it is given
  (`--crl`): a list has to be signed by the issuer it names and be current, and a certificate on it is
  refused. It fetches nothing itself, and says which certificates it was not able to check and where their
  lists are published. In a real document two certificates name a list. The one for the first authority
  under the root is published and was checked; the address the next authority names answered "access denied"
  on 2026-11-15. The two certificates below those name no list and live a day and three hours.
- **Not addressed:** whoever builds the image and whoever verifies it have to agree on the measurements by
  some route an attacker does not control. Today that route is this repository and its CI.

### Weak randomness

- **Built:** on a machine with a Secure Module, random bytes come from it, and if it fails the request is
  refused: nothing falls back to the processor's generator. A machine without a module (an emulator) uses
  the processor's generator. Nothing secret is drawn yet, and nothing here judges how good the module's
  bytes are.

### What the enclave prints

- **Built:** the serial console carries only the image's own status lines. Nothing the parent sends is ever
  printed, so the console cannot be made to say something of the attacker's choosing or to echo data back.

## Not goals

- Protecting anything from AWS.
- Keeping the service available against its own parent.
- Protecting the parent instance.

## Changing this file

A change that adds an input, a device, a secret or a piece of C belongs here in the same commit: what it
exposes, to whom, and what stands in the way. So does a change that adds a dependency to the enclave image,
or puts code in it that also runs on the parent: say why "One flaw is not enough" still holds.
