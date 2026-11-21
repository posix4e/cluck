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

**The input.** Anyone who can reach TCP port 5005 can send a request of up to 32 MiB, which is what a block
of mainnet with its witness needs room for (the largest seen was 22 MB). `Evm/Service.lean`
reads it in Lean, with every length checked against what is left of the request; Jaune's own decoder then
reads the blocks. The C added here never looks at a byte of it: `evm/rt/names.c` passes numbers through to
Lean, and the other two files hold no data at all.

**Time and memory.** A block's time does not follow its gas: of 100 blocks of mainnet the slowest took 70
seconds in the guest for 47M gas, and another took 26 for 60M. A pairing check costs far more time for its
gas than most of what a block does, and nothing here bounds what a sender can make of that.
The machine reads no packet while an import runs, so one request holds off every other client for as long
as it takes, and a sender who wants that can have it. Jaune holds byte strings as lists, many bytes of heap
for each byte of input, on a heap of 256 MiB; a request that needs more stops the machine, which says so.
A request is held as the pieces it came in until it is whole and is then joined once, so for a moment it is
held twice. Eight clients may each be part way through a request, and what is held for all of them together
is kept to 40 MiB (`maxHeld` in `evm/EfiMain.lean`): the client whose bytes would pass that is closed. So
unfinished requests cannot fill the heap, and a sender who holds most of that 40 MiB keeps large requests
from everyone else for as long as its connections live, which is no more than a slow block already gives
it. The largest request seen ran in this heap; one of the full 32 MiB has not been tried and may not.

**An answer with a report.** A frame that begins `JATT1` carries 32 bytes of the sender's choosing and then
a request, and is answered with the response and a TDREPORT whose REPORTDATA is the SHA-256 of those bytes
and the request, then the SHA-256 of the response (`evm/Evm/Attest.lean`). It is the only way this image
asks the processor for a report, so a report from it with other REPORTDATA does not exist. What a verified
quote of that report says is that a trust domain with the quoted measurements answered this request with
this response after the 32 bytes were chosen. It does not say the measurements are of this repository's
source: that is for whoever relies on it to establish, by building the image and firmware and comparing.
The hash is Jaune's SHA-256, the one behind the EVM's precompile; the fixtures exercise it through the
precompile and `evm-test` holds it to three of the standard's examples. Nothing is secret here, so the
report protects no confidentiality: it says who computed an answer, not that the request was hidden from
the host. Outside a trust domain the answer carries no report.

**The page (`evm/demo/`).** `demo/server.py` is a web server on the host, outside the trust domain, and is
in no image. It is the adversary of the demonstration it gives: it starts the guest, carries frames to it,
and has the host's quote generation service sign the guest's report. It can refuse to answer, answer slowly,
or run some other image; it cannot make a quote that verifies with these measurements over an answer the
guest did not give. A visitor chooses one of the fixtures, one of three alterations and a challenge, so no
bytes of a visitor's own reach the guest, and one request runs at a time. `demo/verify.js` checks the quote
in the visitor's browser: the signatures from the quote up to Intel's SGX root key, written in the file, and
the signer of the quoting enclave. It does not fetch Intel's TCB information or revocation lists, so it
accepts a quote from a processor whose firmware Intel no longer considers current, and it is served by the
same host it is checking; a visitor who doubts the host reads the file or uses a verifier of their own on
the quote the page offers for download.

**A block with a witness.** A request that begins `JWIT1` carries one block, the headers before it and a
witness: trie nodes, contract code, and the addresses and slot numbers behind the hashed keys
(`evm/Evm/Stateless.lean`). All of it is the sender's, and none of it is believed. Nodes are found by
their hash from the parent's state root down, which is in the parent header, whose hash is in the block;
`evm/Evm/Trie.lean` reads them in Lean, strictly, and a node that is not there is "missing", never empty.
Code and keys are matched by hash. The fork is the sender's choice unless the request asks for mainnet's
schedule, so an answer about a mainnet block is worth something only if it did.

What is new here is a way to be wrong that the whole-state request does not have. Jaune reads an account
it was not given as an account that does not exist, so a witness that leaves one out makes the block run
on a state that never was. Three things stand in the way. After the block has run, every account and slot
it read must have been supplied or be proven absent; what it read is recorded by this package's branch of
Jaune, in the interpreter and in the preparation of each transaction. Every account and slot that exists
after the block and was not supplied must be proven to have been absent before. And the new state root
cannot be computed without the nodes on the path of everything that changed. If any of these fails the
answer is status 6, which is no verdict. A block rejected while it runs is answered with status 8, also no
verdict, because the reads up to the rejection are lost with it; so a sender can always turn a good block
into "no verdict", and never into "invalid".

What that rests on is the read record being complete, and nothing proves it is. It was written by Jaune's
author for another purpose (the access list Amsterdam puts in a block) and extended here to the forks
before it. `stateless-test` leaves every piece of every witness out in turn and found three reads that
went unrecorded, which were then closed; that it then found none was evidence about the fixtures it runs,
which hold no EIP-7702 authorization, no blob and no withdrawal, **and it was not enough**. On 2026-11-21 a
fourth was found, by the node refusing a block the guest had built: before Amsterdam, Jaune records
nothing of the account a contract calls. For as long as stateless requests had been accepted, a witness
that left out an account only ever reached by a call from a contract got that account taken for empty and
the block run on a state that never was. Put to one block of mainnet with each of 77 addresses left out
of its witness in turn, the code as it stood answered "invalid" 32 times for a block that is valid. So the
sentence above, that a short witness is answered with no verdict, was false of every image built before
that day, and every "invalid" one of them gave is worth only what the witness it was given was worth.

It is closed the way the others were, by recording the read: the account called and the account whose
code runs for it, at the point every call instruction prices the call. `stateless-test real` and
`build-test real` now leave addresses out of the witnesses of real blocks, where contracts call contracts
that nothing else names: 225 witnesses of three mainnet blocks, none answered wrongly; and no block built
from 114 that the checker refuses. What this shows is that four holes were found by looking and one by
accident, not that there is no fifth. An answer of "valid" also says nothing of
the parent: it is about this block on that parent, whatever chain the parent is or is not part of.

**The makings of a block.** A request that begins `JBLD1` carries a header to be filled in, transactions
that are proposed, and a witness, and is answered with a block made of them (`evm/Evm/Build.lean`). All of
it is the sender's. What stands in the way of a wrong block is what stands in the way of a wrong verdict,
used one transaction at a time: a transaction that read anything the witness does not prove is thrown away
with its effects, the block as a whole has to pass the same checks of what was read and what was made, and
the header in the request is held to the parent by Jaune's `validateHeader` before anything runs. So a
short witness gives a smaller block or none. `build-test` leaves every piece of three witnesses out in turn
and puts each block that still comes out to `Evm.Stateless` with the whole witness: 404 shortened
witnesses, none built a block the checker refuses. That is the same kind of evidence as for the checker,
and rests on the same record of reads, which nothing proves complete.

What an answer says is narrow. It says the block is valid on the parent state the witness hangs from and
that, of the transactions proposed and provable, those that went in are in the order the rule gives. It
does not say the sender proposed every transaction it knew of, or proved every account it could have: the
sender chooses what is proposed and can keep a transaction out by leaving its signer unproven. It says
nothing about the slot's inputs (time, randomness, withdrawals, fee recipient), which are the sender's and
come back unchanged. Nobody is asked to keep the transactions secret: they arrive in the clear from the
host. And the guest signs nothing yet, so a block built here binds no one until something outside signs a
bid for it.

**A signing key.** The machine now holds a secret: a BLS key, drawn from the platform's randomness when it
starts (`drawKey` in `evm/EfiMain.lean`), with which it signs the builder's bids (`evm/Evm/Bid.lean`). It is
the first secret this package has held, and what follows is what protects it and what does not.

*What the key is worth.* It guards no funds. Whoever has it can sign bids in this builder's name: say that
a block pays a proposer what it does not, for which a relay that checks blocks refuses the bid and one
that does not would hold the builder to account. It is gone when the machine stops, and a new one is drawn
at the next start; nothing seals it and nothing carries it over. Its public key is answered to anyone who
asks (`JKEY1`), with a report when the request is wrapped in `JATT1`, which is how someone outside learns
that this key belongs to this image.

*What it will sign.* Only a bid for a block it has just built, in answer to the request that asked for it.
The block hash, gas used and value are worked out here; the parent hash, fee recipient and gas limit are
read off the header built; the slot, the proposer's key and the fork version are the sender's and are
signed as given. No request signs a message of the sender's choosing, and the domain is fixed to the
builder's, so a bid cannot be made into a consensus message. The sender can have as many bids signed as it
likes, for any slot and proposer it names.

*Time.* The rule is the OS's: a secret never passes through `Nat` or `Int`, and decides no branch, no
address and no division. Jaune's own BLS code is on `Nat` and is not used on the key. `evm/Evm/Sign/` holds
field elements as fifteen 26-bit limbs in machine words; where a value decides something, both answers are
computed and `Secret.select` (checked in `Mini/Constant.lean`) picks one; points are added by one formula
that is right in every case, so nothing asks which case it is in; and the multiplication does a doubling
and an addition for each of 255 bits whatever they are. Hashing the message to a point and writing the
signature out are public and are `JauneConsensus`'s.

What holds that: for correctness, `bls-test` (54,850 field operations against `Nat`, 242 sums of points
against Jaune's in every case the formula covers, the public keys and signatures of 23 keys byte for byte
`JauneConsensus`'s, a bid's hashing against `JauneConsensus`'s and against a registration a validator
signed for a relay on mainnet). For time there is less. `evm/scripts/check-secret-code` reads the image's
own machine code: the product, the sum and the reduction have no conditional jump and no division; the
difference and the choice have four jumps each, read by hand to be on the reference counts of their
arguments. The curve arithmetic above the field is not read by that script. Nothing was measured on a
running guest. The OS's checker covers the two functions of `Mini/Secret.lean`, not Lean code that calls
them, and the Lean and C compilers are between this source and the machine. The host can time the guest
as finely as it likes, and can ask for as many signatures as it likes. So "constant time" here means
written to be, and found to be in the places looked at, not proved. Two things are not constant time and
are not meant to be: drawing the key throws away a draw that is not below the group's order, which says
only that a draw was thrown away; and the key's bytes come from the platform's random source, which on
this target is the processor's, and is trusted.

*Where the key lies.* In the machine's memory, as four words in a Lean object, for as long as it runs. The
runtime zeroes a block when it frees it, but this one is never freed. Nothing here stops the firmware,
which shares the address space, from reading it; and the request reader, the trie decoder and Jaune all
run in that same space on bytes the sender chose, with a stack that has no guard (above). A flaw in any of
them that let a sender read memory would give up the key.

**A branch of Jaune.** The image now holds `posix4e/jaune`, twelve commits ahead of the upstream commit
this section was written about. Four of them change how something is computed and prove the result the
same (how EVM memory grows, a polynomial division, and what holds the machine's state while an instruction
runs, the last through four theorems that the compiler is told to use). One makes the compiled code differ
from the definition on purpose: `accessDelegation` as compiled records two more reads than as defined (the
fix above), because writing them into the definitions of the four call instructions means carrying their
gas and canonicity proofs across, which is owed. Three put code in the image that
nothing proves equal to what Jaune defines, so compiled code and specification can differ in three places, each of which decides whether a
block is valid:

- whether a jump lands on an instruction (`jumpable`, compiled as `jumpableCompiled`: the compiler makes
  this substitution itself, and the branch's own list of such things says so);
- who signed a transaction (`secp256k1.recoverFast`, on a field of fixed-width words, called where
  `recover` was);
- whether a bn254 pairing check passes (`bn254Pairing` and `bn254FinalExpFast`, called where `pairing`
  was).

What holds them to the definitions is testing, and the user of this repository has said that is enough for
now: comparisons in Jaune's build and in `evm-test` (26,784 positions of made-up code against the proved
`jumpdestOk`; 3,000 made-up signatures against `recover`; field arithmetic on every pair of some 130
awkward values against `Nat`; the fast pairing against the reference on two pairs of points), Jaune's own
Osaka, Prague and BPO2 suites and its curve oracle, all passing on the branch, and 121 blocks of mainnet
whose state roots come out right, which they would not if one sender were recovered wrongly (there are
29,812 transactions in 100 of them).
None of that is a proof, and a block made to find the difference has not been looked for.

**A plain answer still proves nothing.** A request without the `JATT1` prefix is answered over cleartext
TCP with no report, and that response is worth what the network between is worth.

**One secret is held**, the signing key above, and nothing else. Everything but the key's own arithmetic
is on `Nat` or on code that branches on its values, takes time that depends on them, and must never be
given a secret: that is the reason the key's arithmetic was written apart from Jaune's.
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
