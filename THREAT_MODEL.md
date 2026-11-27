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
device-facing memory and network queues for the lifetime of the application (the builder's image
changes two things in them, for a hole under its stack: `efi_guard`, below). The patched network driver checks completion counts, lengths and descriptor
IDs at runtime and selects DMA buffers from driver-owned records. Its code processes
I/O below the Lean Ethernet parser. The Nitro boot stub's W^X and stack-guard checks do not
exercise this path.

A program on this target can also take a PCI device from the firmware's drivers and drive it itself
(`Kernel/Hw.lean`, whose C half here is `boot/efi/hw.c`). A probe does (`pci-probe`), and so does a test
image, `flat-os`, which serves three fixed pages over a trial TCP on a driver of this project's own for the
virtio network card (`Kernel/Net/VirtioNet.lean`). Since 2026-11-23 the builder's images do too: the
service takes its frames from that driver (`Kernel/Net/Wire.lean`) and its TCP is the system's as before;
the firmware's network driver is then not in its path, and the firmware's PCI and page-sharing code are.
Since 2026-11-24 the same images drive Google's card as well when that is the card the machine has,
and take from which card it is where they are: with the virtio card the gateway and name server of
QEMU's network; with Google's the first address of the subnet as the only way out, the metadata
server (169.254.169.254) for names, and segments forty bytes less than the packet size the card
gives. The host shows the card, so the host chooses between the two; it already carried every frame
and could answer any name with any address, and what the machine trusts of a relay is its
certificate under the roots in the image, not the way there. On Google's firmware there is no
network driver to fall back to: a card that will not come up leaves the machine saying so and
stopped.
The OS's own image and the demo still use the firmware's driver. What that C exposes, and what stands in
the way:
- It reads any device's configuration space and, for the one device claimed, its registers and an arena
  of memory shared with it. All of it goes through the firmware's PCI protocol, so the firmware's PCI
  bus driver, its register access and, in a trust domain, its code that makes pages visible to the host
  (`IoMmuDxe`) are in the path of every such access, as they are for the firmware's own drivers.
- It decides nothing about what it reads. Which device to claim, what a capability or a register means,
  what a queue holds: that is Lean. The C checks only that a register lies in one of the claimed device's
  windows (the firmware checks it again) and that memory copied in or out lies in what the arena has
  handed out. Lean is never given a pointer, so a wrong number from a device or a mistake in a driver
  can stop the machine but cannot reach the heap, the stack or the code.
- In a trust domain the arena is memory the host can read and change at any moment, and every register
  access is a call to the host, which answers what it likes. A driver must treat what it copies out of
  the arena, and every register it reads, as the host's word: read once, checked, and not read again.
- The firmware's driver for the device is disconnected when the device is claimed, and the device is
  held so that the firmware cannot bind it again. An image that claims the network card no longer has
  the firmware's network driver under it at all.
- The driver for the network card keeps to that: it copies what the card has finished out of the shared
  memory once and looks only at its copy; the count of finished buffers is cut to the queue's size, a
  buffer's number is taken modulo the size, a length is cut to the buffer's; it never reads a descriptor
  back, and asks the card for no feature that would hand it a frame unfinished. It trusts the card to
  finish transmit buffers in the order they were given: a host that does not can spoil frames on their
  way out, as it can anyway. None of it has been tried against a card that misbehaves on purpose.
- A queue's position is two bytes that an honest card changes while the driver reads them. Read a byte
  at a time they came out half old and half new about once in some thousands of batches, a position 256
  away, and a whole queue of old frames was taken again, or sent again by the card. They are now read
  and written in one go (`silo_hw_load16`, `silo_hw_store16`). It was found by two guests under load on
  separate processors and by nothing before that: a test on one processor does not show it.
- The driver now believes one more word of the card's: that it is looking at a queue already and need
  not be told. A card that says so and is not looking gets no frames from the guest and gives it none,
  which the host can bring about anyway by carrying nothing. So that an honest card and the driver
  cannot each miss the other, `silo_hw_store16` ends with a full barrier (`__sync_synchronize`): the
  position written is seen by the card before the driver reads the card's word.
- For the builder this moves a line. Before, the firmware's driver stood between the host's queues and
  the service, and a frame reached Lean as bytes the firmware had copied. Now the words of the host's
  queues are read by this project's driver, which is younger and less tried than the firmware's; what
  it does with them is in Lean, each number cut to what it can be, and it has been run for a few
  hundred slots, not a thousand, at the time of writing. A wrong word still cannot reach beyond the
  shared arena. The service also no longer sleeps a millisecond whenever no frame is there: it looks
  again at once some twenty thousand times first, so a host that trickles frames keeps it busy, as a
  host can by other means.
- The runtime's `memcpy` and `memset` (`rt/bare/libc.c`) are `rep movsb` and `rep stosb` on x86-64 where
  they were loops; they read and write what they were asked to and decide nothing. Every image changes
  by it.
- `silo_hw_load32` reads four bytes of the shared memory in one go, for a count the device keeps
  adding to. And there is a second driver on this interface, for Google's network card
  (`Kernel/Net/Gvnic.lean`): what it takes from the card (queue lengths, doorbell numbers, lengths of
  frames) is cut to what it can be before it is used, as in the first. It was in no image that
  served anything until 2026-11-24; now it is in the builder's, under the system's TCP, and has
  carried the builder's requests and its connections to the relays on Compute Engine. It is newer
  and less tried than the other, and can only be tried there: QEMU has no such card. The card
  can start over by itself, or say by a bit of its status that it wants to be started over, and
  is then reset and made ready again in the same memory: while it is being brought up, for most
  of a minute if need be, and whenever the machine, asking once a second, finds that it has.
  A host that keeps doing so keeps the network down, which it can do by not carrying frames.
- `silo_hw_write_direct` stores to a register of the claimed device by the processor's own
  instruction, at the place the firmware says the device's window is, where every other register
  access asks the firmware. It is checked to lie in a window like the others. It is there because in
  a trust domain the firmware turns each access into a request to the host, and a register that is
  hardware (the doorbells of Google's card) is not reached that way. What it leans on that the
  others do not: that the firmware has mapped the device's windows as memory the host shares, and
  that its word on where a window is, is right; a wrong word would be a store somewhere else in the
  machine's addresses, which no check here would catch.
- `silo_efi_quote_ask` (`boot/efi/platform.c`, 2026-11-24) asks the host for a quote: it asks the
  TDX module how wide a guest address is (TDG.VP.INFO), which says which bit marks an address the
  host may see, and then tells the host, by the call the specification has for it
  (TDG.VP.VMCALL, GetQuote), the address and length of a run of whole pages of the arena shared
  with the claimed device. The run is checked to lie in the arena, as every access to it is
  (`silo_hw_shared`, which is that check under a name another file can call). It reads one number
  back, the host's word on whether it took the request, and hands that to Lean. It never looks at
  what is in the run: Lean wrote the request there and reads the answer (`Kernel/Quote.lean`).
  What is new for the host: nothing it could not do before, since the arena is memory it can
  already read and write at will; it is told which part to write an answer in.
- `stop_clock` (`boot/efi/platform.c`, 2026-11-25) stops the firmware's clock when the image
  starts, through the firmware's own service for it (the timer protocol), and never sets it
  going again. Firmware keeps a timer interrupt going every 10 ms for as long as an image runs
  under it, and its handler then runs, on the image's stack and between any two of its
  instructions, whatever firmware has waiting on time. Nothing in the image waits on it: time is
  the processor's counter, and the one sleep asked of firmware is a counted delay. With it
  stopped, firmware's code runs when the image calls it or does something only firmware can
  finish (a device register, the console), and not otherwise. There was a second reason, which
  is how it was found: on Compute Engine, where the host makes a quote before the call for one
  returns, about one call in ten with that interrupt due meanwhile ended the trust domain and
  started it afresh with new keys (`TODO.md` has the trials; why the host does that is not known
  here). What it leans on: the firmware's word that the service does what its name says. Where
  firmware has none, or refuses, the console says so and the image runs as it would have.
- `efi_guard` (`boot/efi/guard.c`, 2026-11-25; in the builder's images, not in the running one
  until it is deployed, which `TODO.md` says) makes a hole under the stack the builder runs on,
  and is the first thing here to change what firmware set up instead of asking firmware. It
  walks firmware's page tables from the processor's root to the entry of each page of the hole;
  where firmware mapped that memory as part of a 1 GiB or 2 MiB page it puts in a table of 512
  smaller pages saying what the large one said (from eight pages of the image's own), and it
  marks the hole's pages absent. It clears the bit of CR0 that makes read-only pages read-only to
  the machine itself for as long as it writes, since some firmware keeps its tables so. And it
  copies firmware's table of segments, with a task segment added, and firmware's table of
  exception handlers, with the entries for a page fault and a double fault pointing at 20 lines
  of its own on a stack of their own, and has the processor use the copies. Every other
  exception goes to firmware as before, the one a trust domain takes when it touches a device
  among them. What it reads is firmware's own tables, never a byte from outside the machine; an
  entry it cannot follow is refused and the image stops, saying so. What it leans on: that
  firmware goes on working with its segments and handlers in a copy (it did, on the three
  firmwares tried: OVMF emulated, TDVF in a trust domain here, Google's), and that nothing of
  firmware's later maps the hole back in. What is new to go wrong: a mistake in the tables it
  writes is a machine that stops, or memory mapped that should not be, with nothing but
  `scripts/stack-check` and the fixtures to say it is right; it was written by hand, in C, 199
  lines, and is not printed from the small language as the Nitro target's mapping is. A page
  fault from any cause now ends in this file's handler, which says where and stops, where
  firmware's would have printed the registers and hung.
- `silo_hw_store32` writes four bytes of the memory shared with a device in one go, checked as the
  other stores are; the driver's copies to and from that memory are made by `rep movsb` in
  `boot/efi/hw.c` and not by the runtime's `memcpy`. Neither reads anything.
- `silo_hw_ticks` reads the processor's time-stamp counter, for a program to see where its own time
  goes (`flat-os` prints it). It takes nothing from the host; in a trust domain the counter is kept by
  the TDX module. A program that put secrets and such timings side by side would have to think about
  what the timings say; nothing here does.
- The card may be carried on the host by a program of its own in place of the kernel (vhost-user,
  `SILO_NET_VHOST_USER` in `scripts/run-efi`; used for measuring only). Nothing changes for the guest:
  it is the same card, the same queues in the same host-visible memory, and the host was already
  trusted with nothing in them. Whether QEMU hands such a program only that memory in a trust domain
  was not checked from the host's side.

The host and anyone on the network can observe, change, replay or drop Ethernet traffic.
ARP and Neighbor Discovery establish reachability. Neither authenticates a peer. The demo
serves cleartext TCP and UDP, and exposes its framing and transport state to remote clients.
The guest bounds TCP connections, buffered stream data, fragment assemblies and their lifetimes.
An attacker can still occupy those limits, withhold acknowledgments, exhaust CPU time or
prevent the firmware or virtual NIC from making progress. The system's TCP (`Kernel/Net/Tcp.lean`)
now offers a peer a window of two megabytes, where it offered 8 KB, and keeps what comes ahead of a
gap: up to 2,048 segments a connection and 4 MiB over all connections (`maxEarly`,
`maxEarlyBytes`), where it kept one segment. That is memory a peer can make it hold for as long as
its connection lives, on top of the 128 KB a connection may have waiting to be sent, and the walk
through what is kept is in the order of its length for each segment that comes out of place. How
fast it sends is now steered by the peer's acknowledgements: a peer that acknowledges early or
never can make it send faster or slower to that peer, within what was already handed over to be
sent, and can make it send a segment again; it cannot make it send what was not meant for that
connection, and an acknowledgement of bytes never sent is refused as before. No secret should be exchanged on
the strength of a TCP connection or checksum.

The EFI image and its firmware are separate inputs to measurement. A TDREPORT binds the 64
caller-supplied REPORTDATA bytes to the local TD. The host-side QGS helper transports it to
Intel's quoting service and returns the quote bytes. Where there is no such helper to go to (a
cloud's machine), the builder's image asks its host for the quote itself (`Kernel/Quote.lean`,
and "JQUO1" in `evm/Evm/Attest.lean`): the status and length the host writes back are read as
the host's word (twice, until two readings agree; cut to the room there is), and the quote is
bytes for someone else to check. A host can refuse, be slow, or write nonsense. The machine
waits up to five seconds and does nothing else meanwhile, so whoever can reach its port can
have it stand still that long a request, as they can by other requests; a host that takes a
request and never finishes it gets no more. (A host that makes the quote before it returns
from the call, as Compute Engine's does in some 40 ms, holds the machine for as long as it
takes, whatever the five seconds.) What is asked for is a quote of a report handed
in, and reports are made by the machine only of answers it gave, so nothing can be quoted
that the machine did not say; a report made by another trust domain on the same host could be
handed in and would be quoted, which lends out the host's quoting service and nothing of this
machine's. A relying party must verify the signature
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

**Code of this project's in Jaune's place.** `evm/Fast/` is the start of an engine written for speed, to
take Jaune's place piece by piece in what runs. The first piece in use is Keccak-256 (`Fast/Keccak.lean`):
the witness trie now names and checks every node by it (`Evm.Trie.hashOf`), so a state root, and whether a
witness node is the one its hash names, rest on it. Nothing proves it equal to Jaune's or to the standard.
`evm-test` holds it to Jaune's on 614 inputs, every length from none to 300 bytes and some of many blocks,
and the tests and saved blocks that compare roots with a node's would fail if it differed where they look.
The EVM's own KECCAK256 and Jaune's tries are still Jaune's.

A second way in runs the rest of the engine. A request whose first five bytes are `JWIF1` is a stateless
request in every other byte and is judged by the engine (`Evm/Engine.lean`): this project's interpreter,
state, transaction and block rules, with Jaune still deciding what needs no state (the header against its
parent, the decoding of blocks and transactions, the recovery of senders), still running the precompiled
contracts, and still making three of the roots. The engine reads the witness itself, a question at a
time: when it comes to an account or a slot it looks for it in the trie by the hash of the address or
number it has in hand, and the answer is the entry found, or a proof that there is none, or that the
witness does not say, which marks the engine's world and is never taken for "not there". So the addresses
and slot numbers a stateless request carries are not used on this way in, and leaving them out changes
nothing. The answer says "valid" only when the gas used, the five roots and the requests hash the engine
arrives at are the header's, by the same comparison Jaune's path ends with, and only if its world is not
marked. A refusal by an engine whose world is not marked is answered as a verdict (3), where Jaune's path
answers 8, no verdict, because Jaune cannot say what it had read. What holds the engine: its arithmetic
to `Nat` on 5.9 million cases; its interpreter to Jaune's on 170,000 programs that need no world; 121
blocks of mainnet, whose headers it reproduces in every field compared; and `stateless-test`, where on 279
blocks of test chains it gives Jaune's answers, on 1,143 witnesses with one node, key or code left out it
gives the right answer (734, the keys among them) or none (409), never another, and a block that lies
about its state root is refused; and Ethereum's own tests of chains for Prague, Osaka and the two forks after
(execution-spec-tests' blockchain tests, 4,723 files), where it accepts every block it should and refuses
as invalid every one of the 3,575 it should. Nothing proves any of it. The tests say why a block is to be
refused and the runner checks only that it was. A block of a fork before Prague is not judged by the
engine at all: it answers that it has no rules for it. A flaw in it that made a block's wrong execution agree with a header would
have to match what the block's maker claimed; a flaw that makes a right block disagree is a false
"invalid", which is the likelier kind. Both paths are in the image; nothing but the first five bytes of a
request chooses between them. The builder has the same two ways in: a request to build that begins `JBLF1`
is built by the engine, and since a request for a bid carries a request to build of either kind, the
machine's key signs for a block the engine built as readily as for one Jaune built. What that adds for
whoever takes the bid: a flaw in the engine can make a block whose header claims what running it does not
give, which a relay's own check then refuses, at the builder's cost and nobody else's. `build-test` has
Jaune's checker judge every block the engine builds in it.

**The image that builds for relays has only the second way in** (since 2026-11-25). `evm-os`, and its
twin that knows the stand-in, answer a request to build that begins `JBLF1` and a block to judge that
begins `JWIF1`, besides what the machine itself answers (bids, keys, sealed transactions, the chain's
next block, posts to relays). A request for Jaune to import a chain, to judge a block or to build one is
answered 5, as if it were no request. Jaune's interpreter and its running of a transaction are not in
that image: nothing the machine calls leads to them (`Evm.serveBuilder`, `Evm.Serving.builder`), the
linker drops what nothing calls, and `scripts/build-efi` refuses to make the image if the linker's map
names any of four of Jaune's functions that every way of running a transaction goes through. So "both
paths are in the image" is now true of `evm-os-spec` alone, the image for the fixtures and for the page
that shows a guest answering them, which opens connections only to the stand-in and has a measurement of
its own. What this takes away: whoever feeds the machine could before choose, by five bytes, to have its
key sign for a block built by code this project has not reviewed, and could reach all of Jaune's rules
with bytes of their choosing. What it does not: the engine already built every block that was bid, and
nothing more holds it than did; and nothing in the image compares it with Jaune any longer, which only
the tests do, elsewhere. What of Jaune is still in the image, 0.76 MB of its 4.0 and reached on every
request: its types for headers, blocks and transactions and their decoding from RLP; the check of a
header against its parent; the recovery of a transaction's signer; the roots of a block's transactions
and withdrawals; its precompiled contracts, all of them, since its table of them is linked whole though
the engine runs its own for the three on bn254 (SHA-256, RIPEMD-160, BLAKE2, the two secp256 curves,
modular exponentiation, BLS12-381, KZG); and the public half of the BLS used for bids. The guard is four
names (the step of a message, the run of plain instructions, the end of a call, the running of a
transaction): Jaune's code that got in by another road would show in `scripts/image-inventory`, which
counts it, and not in the build.

On that second way in, three precompiled contracts are this project's too: addition and multiplication on
bn254 and the pairing check (`Fast/Bn254.lean`), which is what zero-knowledge verifiers on the chain call.
A pairing check that said yes to a false proof would let a block that accepts the proof look valid only if
the block's maker had claimed the same; one that said no to a true proof makes a valid block look invalid.
`bn254-test` holds the three to Jaune's on some twelve hundred inputs, among them every way of being
malformed it could make but one: a point on the twisted curve outside the pairing's subgroup, which the
code refuses by multiplying by the group's order and which no test here has shown it refusing.

**Cryptography of this project's own.** `evm/Tls/` is what the guest needs to keep a transaction from
the host: hashes, HMAC and HKDF, ChaCha20-Poly1305 and X25519, in Lean, because the rules here let nobody
else's into an image. It is in the image now and is what a connection out rests on (below). It is
held to OpenSSL and to the standards' printed examples by `tls-test`, not proved, and it has not been
reviewed by anyone who writes such code for a living. For time: no secret goes through `Nat`; the field
of X25519 and Poly1305 is fixed-width limbs with no branch in the source on a value; the ladder's choice
is the OS's `Secret.select`; a tag is compared by `Secret.equal`. What the compilers made of it was looked
at as the signing key's arithmetic was (`scripts/check-secret-code lib`), which counts jumps and does not
prove their absence where it matters, and one branch on a key's bit was found that way and removed.
Nothing was measured on a running machine. The key exchange's private key is drawn from `RDRAND`
alone, like the signing key, a new one for every connection. Beside it is what decides whether the far end of a connection is the
relay it claims to be (`Tls/X509.lean`): a reader of certificates and a walk up a chain to a root built
into the image. It reads bytes that anyone on the path, the host first, can choose, so it is written to
refuse whatever it does not expect, and a certificate it cannot read is a refusal. What it does not do is
said in its first lines and matters: nothing is checked for revocation, so a relay's stolen key is good
until its certificate runs out; and "runs out" is judged by a time the caller supplies, and the guest has
no clock but what the host tells it.

The client that uses these (`Tls/Client.lean`) is written to be small before anything else: TLS 1.3
only, one key exchange, one cipher, no resumption, no early data, and a refusal for every message it does
not expect. Every byte it reads before the server's finishing word is chosen by whoever is on the path,
which for the guest is the host. What it relies on: that the server's proof of its key is checked over
everything said so far, that the finishing word is checked before any data is believed or sent, and that
keys never change in the middle of a record; each of those has conversations in `tls-test` that fail if it
is taken out, and that was tried. What it does not do: it sends no alert, so a server learns nothing of
why it was dropped; a key that is dropped is not wiped from memory; the lengths of records, and so
roughly of what is said, are plain to the carrier, and it pads nothing. It is tested against OpenSSL's
server and against one written here, and is neither proved nor reviewed.

**A second secret, and other people's.** The machine now holds a key that opens what is sealed to it
(`Evm/Seal.lean`: X25519, drawn from `RDRAND` when it starts, never written anywhere), and, for a few
slots each, transactions that were sealed to it and that nobody else on this side of the relay is meant
to read. What that rests on, and where it gives:

- *The key's arithmetic* is the X25519 of `Tls/`, with what was said of it above: no secret through
  `Nat`, no branch on a key's bit that reading the compiled code found, nothing measured, nothing proved.
  Opening is HPKE as RFC 9180 has it (`Tls/Hpke.lean`), held to OpenSSL's on messages OpenSSL sealed.
  Unlike a connection's key this one lasts as long as the machine runs and is used on bytes anyone can
  send as often as they like, which is what an attack by timing needs; the tag is checked in constant
  time and a failed opening says one byte, the same whatever went wrong inside the sealing.
- *An opened transaction is ordinary data* to everything after it: Jaune decodes it, the engine runs
  it. None of that code was written to keep its input secret, and its time and memory depend on the
  transaction. The host sees how long a block took.
- *What the host is told on purpose.* For a transaction sealed without proofs: which accounts and
  which slots of storage it touched and the witness did not prove, since the guest has no state and
  must ask. That there were sealed transactions to try in a block. Not the block, and not whether
  they went in: the answer then carries no header, no hash and no value, because the host has the
  chain's state and could check a guess against any of them.
- *A sender can bring the proofs*, and then the host is told nothing of what the transaction touches
  (`Evm/Seal.lean`, "With proofs"; `Evm/Follow.lean`). The guest keeps such proofs good by following
  the chain: it is shown every block with the block's own witness, checks it, and keeps what it wrote.
  That adds things to say:
  - The guest checks that each block follows from its parent by the EVM's rules. It cannot check that
    the chain is the one validators agreed on, so the host can show it a chain of its own making, as
    long as each block on it is valid. A sealed transaction built on such a chain goes into a block no
    relay will take. The host cannot make up state freely that way, since state only changes by
    transactions somebody signed and by the block's own rules, but it can choose among real pending
    transactions and order them, and see afterwards whether the sealed transaction went in.
  - Whoever asks for blocks also chooses what else is proposed, and was at first told whether the
    sealed transaction went in. Over several blocks that is enough to learn roughly what it pays and
    how much gas it allows, by filling blocks to different levels and watching; so it is no longer
    told (below). How long the block took is still seen, and one transaction more or less is within
    what that varies by anyway, though nothing here measures how well that hides it.
  - The sealed bytes are longer the more state the transaction reads: 13 KB for a call that reads one
    contract and one slot. Their length says something, and nothing pads it.
  - Proofs are bytes the sender chose, read by the trie code (`Evm/Trie.lean`), which already reads
    witnesses from the host. Each node is found by its hash from a root in a header the guest checked,
    so wrong nodes prove nothing; too many are refused by size.
  - A transaction whose proofs fall short of what it reads is left out and nothing is said, to the
    host or to the sender. The sender finds out by its not being built.
  - A block the guest must follow can take seconds to check (9 s was seen for one). While it does, no
    block is built, and a host that wants to keep proofs from being used can simply not show blocks.
  - Checking every block of the chain is the heaviest thing the guest does, and it ran out of memory
    doing it on a 256 MiB heap; the heap is 512 MiB now, and 100 blocks in a row take 246 MiB of it.
    A block with a larger witness than has been seen could still end the guest, which loses its keys
    and everything sealed to it. The host chooses what the guest is shown, so the host can do that
    at will; it could always stop the guest at will.
  - What the host is no longer told: whether a sealed transaction went into a block (the answer says
    only that there were some to try), and how long what the guest sent to the relay was, except to
    the nearest 16 KB (padding inside TLS). It still sees how long the block took to build.
  - One thing more is told since blocks are built all through a slot: a block that pays no more than
    one a relay has already taken for the slot is not sent, and the answer says nothing was sent. For
    a block with sealed transactions tried, that is a comparison of two payments the host is not
    otherwise given by this machine. A relay's list gives both payments outright.
  - And one more since 2026-11-24: a block that pays the proposer nothing is not sent either, and
    the answer says nothing was sent. With sealed transactions tried, that tells the host that
    none that went in paid anything, which a relay's refusal of the block told it before.
  - **What a relay publishes, which undoes part of that.** Found on 2026-11-22, after two blocks had
    been sent this way. A relay lists every bid it receives, for anyone to read
    (`/relay/v1/data/bidtraces/builder_blocks_received`; Flashbots, Ultrasound and Aestus were seen
    to, and Titan gave no answer when asked): the block's hash and parent, the gas it
    used, what it pays, how many transactions are in it, and when it arrived, to the millisecond.
    The host knows the builder's key and exactly what it proposed. So against a real relay it learns
    at once, from the relay, whether a sealed transaction went in, how much gas it used and what it
    paid, whatever this machine declines to say; and the hash lets it check a guess at the whole
    block. What this machine keeps back is kept back only where the relay publishes nothing (the
    stand-in on the host does not), or for a block no relay takes. What a real relay's list does not
    give is what the transaction is: who sent it, to what, with what data. That is hidden until the
    block is in the chain, and for good if it never is.
  - **So a host that sets out to can learn what a sealed transaction does, without ever reading
    it.** The host chooses the other transactions of the block and may write them itself; a block
    that is not chosen costs it nothing; and the relay publishes each block's gas and count. A
    transaction of the host's put *before* the sealed one arranges the state it runs in, and the
    gas says how it fared: whether it still succeeds when a price has been moved, for one. A
    transaction put *after* reads what the sealed one changed: one made to fail unless a given
    contract's state is as the last block left it shows, by failing, that the sealed one touched
    that contract, and a few of them over a few slots can find how much it moved a price and which
    way. That is most of what anyone would want to hide a trade for.
  - No rule about order mends this, and several were thought through on 2026-11-22. Sealed
    transactions first, so that nothing of the host's runs before them: the ones after still read
    what they changed. Leave out a host's transaction that behaves differently because of a sealed
    one: its being left out is in the count, and says the same. One sealed transaction to a block,
    or one block with sealed transactions to a slot: fewer answers, each as full. Hide how long the
    block took: the relay's list says more than the time did. What would mend it is a block with a
    sealed transaction and nothing of the host's choosing in it, which is a block nobody picks; or
    relays that publish nothing about bids, which is not this project's to change.
  - What sealing does give, then, said exactly. Against a host that only carries and watches: the
    transaction, who sent it and what it touches are not seen until its block is in the chain, and
    with proofs brought along not even the account is. Against a host that works at it: the bytes,
    the sender and the signature are still not seen, and nothing lets it change the transaction or
    get it built after its last slot; what the transaction does to the state can be found by asking.
    Against everybody else, who cannot put transactions to this machine or tell which bids are its
    answers to what: nothing but the relay's figures for the whole block.
    None of the asking has been tried here; this is reasoning from what the relays were seen to
    publish.
- *What the host can do anyway.* Not hand a sealed transaction in; not prove what it needs, so that it
  is never built; choose, among the slots up to the last the sender named, which blocks it is tried in.
  It cannot have it built after that slot, cannot read it, and cannot change it. It can hand the same
  sealed bytes in again, which gains it nothing: the second copy fails where the first has gone in.
  It can fill the pool (64 transactions, half a megabyte) with rubbish, since nothing is checked at the
  door, and keep honest ones out until the rubbish's slots pass.
- *What the relay sees*: the whole block, as from any builder. *What the console says*: that there were
  sealed transactions to try in a block, never whether one went in or anything of one. `builder/shadow --sealed` searches the
  console and every frame for the transaction's bytes and its signature's numbers.
- *The page that seals* (`demo/seal.html`, `demo/seal.js`) runs in the sender's browser and is served by
  the host, which could serve a different script: a sender who means it checks the script, or seals
  with a tool of their own, which the standard format allows. The page checks the quote for the key as
  the first page checks one, with the same limits (no revocation, no TCB status).
- *Live twice.* Mainnet block 26465583 was built and sent this way, with one sealed transaction in it
  that the host carried and was not shown; for that one the host proved the sender's account, and so
  knew it. Block 26470277 had one that brought its own proofs, from an account named in nothing the
  host handled before the block was public (`TODO.md`). Two blocks show that the parts meet, and
  nothing about how they stand up to someone trying: in both, sender and host were one program on one
  machine.

**Connections out.** The machine now speaks first: it opens TCP connections of its own, to the relays
its image names (`Evm/Relays.lean`), and until now it only ever answered. What that adds:

- *More of the network's bytes are read.* Answers to name lookups and to questions about Ethernet
  addresses were dropped before and are parsed now (`Kernel/Net/Dns.lean`, `Route.lean`, both the OS's and
  both tested, neither proved), and so is everything on a connection out before TLS has judged it. All of
  it comes from the host. None of it is believed: an address for a name, or an Ethernet address for the
  way out, only decides where packets go, and the certificate is what says who answered. So the host can
  make a call fail, slowly if it likes (ten seconds, then it is given up), and cannot make it reach
  anyone else as the relay.
- *Whom it believes is in the image.* Four roots, Let's Encrypt's two and two of Google's, copied from
  this machine's store with their hashes beside them (`Evm/Roots.lean`). Any certificate authority under
  those roots can make the guest believe a server is a relay; that is what trusting a root means, and
  the list is as short as the four relays allow. A second image, `evm-os-shadow`, believes a root whose
  key is public, for a stand-in relay on the host: it is for trying things and protects nothing. The
  two differ in measurement, and a relying party that means the real one must check for it.
- *The date is the host's word.* A certificate is good between two dates and the guest has no clock that
  knows the date; the request names the time. A host that lies can have a certificate believed after it
  has run out, which matters if it also holds that certificate's key, stolen. It cannot go back before
  the day the roots were written into the image, and it cannot make a certificate good that never was.
  Nothing better is on offer inside a trust domain without trusting someone for the time.
- *What a carrier sees of a call.* The relay's name, in the lookup and again in TLS's first message;
  when, how much, and how long. `scripts/run-ask` has QEMU write down every frame and checks that
  nothing else is in the clear.
- *A request that makes the guest ask.* `JASK1` has the guest GET a path from a relay and hand back the
  answer. It can send a relay nothing but that line: the path is refused unless it is plain printing
  characters with no space, so it cannot carry a second request. The sender learns nothing it could not
  fetch itself, except, with a report, that this image got that answer from the server its roots vouch
  for. A sender can keep the guest's thirty-two connections busy this way, as it can by other means.
- *A request that makes the guest send a block.* `JSND1` is a request to build and bid with the sending
  added: the block is put into the builder API's SSZ in the guest (`Evm/Submit.lean`) and posted to the
  relays of the image's list that the sender names. It signs nothing a request to build and bid would
  not sign, and sends a relay nothing but that block and bid; the sender could have posted the same
  itself from the answer, which it still gets. So today this hides nothing: it is the path a hidden
  transaction will need, tried first on blocks that have none. What is new in it to go wrong: a second
  reader of RLP (`Submit.item?`, over a block Jaune has already decoded once), with every length
  checked; and the SSZ itself, which four relays have now read once. The real image has
  this request as the shadow image has, and will send to real relays when asked: whether it is asked is
  the host's choice, as sending always was. A block the guest sends has been judged by nobody before
  it leaves: when the host sent, the node's validator saw every block first.
- *Connections to relays are kept between blocks* (2026-11-24; `Outbound.Line`, `Machine.State.lines`).
  A block's post leaves its connection to each relay open, and the next block to that relay goes on
  it, so the certificate is judged when a connection is opened and not again for each block: a
  certificate that runs out, or a date the host gives differently later, is not looked at again while
  the connection lasts, which is for as long as blocks keep being sent and the relay keeps it. The
  session's keys stay in memory that long, where a call's were dropped with it before. It is the same
  TLS session throughout, so a carrier learns nothing from it that it did not from a connection a
  block, and loses the sight of a handshake each time. What it adds to what the far end can do: send
  bytes on a connection nothing was asked on, which are given to TLS, and the connection is closed
  unless TLS took them in silence (a ticket, which is never used); close it, which is answered in
  kind; or close it as a block is on its way, after which the block is posted again on a new
  connection, so a relay, or the host for it, can have one block posted to it twice. At most one
  is kept a relay, closed after a minute with nothing sent. The questions asked with `JASK1` are
  still a connection each.
- *Who signed a transaction is kept for the next request too* (2026-11-26; `Build.Signers` in
  `Evm/Build.lean`). Finding a transaction's signer is the largest part of what a request costs
  before its first transaction goes in, and the requests of a slot propose mostly the same
  transactions, so a request read with what was sent before (`JBLF2`, the next item) is also handed
  the signers found for the request before it. That is a second thing a block is built with that
  did not come in its own request. What stands in the way of a wrong one: nobody sends a signer;
  each was worked out in this machine from a transaction given to it, is kept under the hash that
  was signed together with the signature, the chain and the kind of transaction, and is taken only
  for a transaction of which all of those are its own, which is everything the working out reads.
  A kept signer is then what working it out again would give, as far as two different signed
  contents do not share a keccak hash, which the signature itself rests on. Bounded by the last
  request built from nothing: only its transactions' signers are kept, with those of the
  transactions that requests going on from its block (below) have proposed since. The transactions the machine adds itself, the
  sealed ones, are neither looked up nor kept (`Request.fromSender`), so how long a request takes
  says nothing of them that it did not before. Checked in `build-test` on the blocks of mainnet
  there: the same block with the signers kept; a signer under another signature, chain or `r` not
  taken; one under the transaction's own taken.
- *A block can go on from the block built for the request before* (2026-11-26; in `03394a79…`, the image
  that runs on Compute Engine since 23:53 UTC that day, whose feed asks for it in every round;
  `Build.Before`, `Build.runGoingOn` in `Evm/Build.lean`). A request that begins `JBLF2` with
  the byte 2 says so, and the machine then keeps, with what the next item describes, the block it
  built as that stood after its last transaction and before anything that ends a block: the
  engine's state, the receipts, and each proposed transaction decoded with its signer. The next
  such request, if it is for the same block, has only the transactions that are new in it run,
  after those already in. This is the first thing kept between requests that is a result of running
  transactions and not bytes found by their hash, so what stands in the way of a wrong block is said
  in full. (1) The same block: the fork, chain, rule, gas and work allowed are compared; the header
  and the withdrawals are the same bytes, by the keccak hash of the proposed block outside its list
  of transactions; the request's headers are a checked chain ending in the header the kept block was
  built on. Everything the running reads of a block's surroundings is one of those. (2) The same
  transactions: each one in the kept block must be proposed again, known by the keccak hash of its
  bytes as they stand in the list, or the request is built from nothing. (3) The state: the engine
  remembers of the parent's state only what a witness proved, found or absent, and never that a
  question went unanswered (`Fast.World`; this was not so of a storage slot until the same day, see
  the next item but one), so the kept state with the new request's wider witness behind it answers
  as a state begun on that witness would. (4) Nothing comes in a request that says what is in the
  kept block or what a transaction's signer is. (5) The state root: what the last one was worked out
  with is kept too (the state's trie as this machine wrote it, and each leaf and slot value written:
  `Bridge.Rooted`), and the next writes only the accounts and slots that are not as they were written
  then (`Bridge.rootGoingOn`). The root of a trie depends on its leaves and not on the steps they
  were written in; the nodes written through are the witness's, found by hash as ever, and the rest
  this machine's own working. If anything written before is not there to be looked at again the
  root is worked out whole. A block that goes on is then a block this machine
  could have been asked for outright, with its transactions in that order under rule 0. What does
  change: under rule 1 the order is no longer what the rule alone would give, since what was in
  before stays before what comes later whatever each pays, and which transactions are in depends on
  the requests before. All of that was the host's already: it chooses what is proposed and when.
  A request the machine adds a sealed transaction to is built from nothing, and what is kept to go
  on from is left as it was (`Bid.buildWith`), so no state that a sealed transaction touched, and no
  timing that depends on one beyond what a request to build already showed, is carried to a later
  request. One block is kept, replaced by each request that may go on and forgotten with everything
  else kept; its size is that of the state the block touched and its transactions decoded, and
  has not been measured: all that is known is that 1,000 slots in a row in a trust domain, 34,298
  requests of up to 13.7 MB with the most kept that the limit lets be kept, did not run the 512 MiB
  heap out. On the console the machine says that a block went on and from how
  many transactions, which the host knows. It also says there, since the same day, how a request's
  time was divided (reading it, the transactions, ending the block, signing), but only of a request
  no sealed transaction was tried in: of one that was, the console says how long all of it took and
  no more, as before, and that much the host times for itself (`Machine.buildWith`). Checked in `build-test` on the blocks of mainnet there:
  a block's transactions proposed in two parts give the very block built at once; the clock running
  out part way gives a block the checker accepts, and the next request finishes it; another gas
  limit, rule, fee recipient, a transaction withdrawn, or transactions added by the machine each
  make it start from nothing; a node the first request lacked, given with the second, lets what was
  left out go in. Not yet run in a trust domain or through the feeder.
- *What a request to build gave is kept for the next* (2026-11-26; `Build.Kept` in `Evm/Build.lean`,
  `Machine.State.kept`). A request to build that begins `JBLF2` is read with the trie nodes, contract
  codes and headers that earlier such requests gave, and what it gives is kept in its turn, so whoever
  feeds the machine sends each of them once and not with every round. Until this the machine carried
  nothing from one request to build to the next but its keys, its connections and the sealed
  transactions; now a block can be built with bytes that came in an earlier request. What stands in
  the way of that going wrong: a kept node or code is found by its hash exactly as one in the request
  is, so it proves what the same bytes in the request would prove and nothing else. A header is
  decoded and hashed when it is given, and joins the kept ones only if each of those given names the
  one before it by that hash; the kept ones are then handed to every request as a chain already
  checked (`Kept.take`, `Request.ancestry`), and that the newest of them is the block's parent is
  checked on every request (`Build.begin`). Until `b1f0683b…`, the image after `a07875d4…`, all 255 were decoded
  and hashed again on every request, a tenth of what a request cost; what is believed in its place is
  that headers this machine checked and has held in its own memory since are the ones it checked,
  which is what it already believes of the nodes. Nothing that comes in a request can say that its
  headers are checked. So nothing kept can make a wrong block, and that rests on the same hashing
  the witness always rested on. What does change: which transactions go into a block, and whether one is
  built, now depends on what was sent before as well as on the request, and all of that is the
  host's, as the request is. Nothing of a sealed transaction is kept this way: the proofs one brings
  are added to the one request they are tried in (`Bid.buildWith`) and not to what is kept, and an
  answer still names what the witness lacked only for the transactions the sender proposed. What is
  kept is bounded by what was given, 16 MiB of nodes and codes counted as they are given
  (`Kept.limit`), after which all of it is forgotten; held in a tree it takes about a third more
  than that of the heap. Anyone who can put a request to the machine can fill it with nodes that are
  nothing, or have it forgotten (a request can ask that), and the feeder's next request is then
  answered as one with a short witness and has to be sent again whole: a round lost, which that
  sender could already cost it by keeping the machine busy. Not measured: the heap with the most kept
  and a request of the longest allowed at once. A request that begins `JBLF1` reads nothing kept and
  keeps nothing.
- *The engine remembered a storage slot it could not read as an empty one* (found and put right
  2026-11-26, `Fast/State.lean`; in every image up to and including `b1f0683b…`, which ran on
  Compute Engine from 19:15 to 23:48 UTC that day; `03394a79…`, which runs there since, has the
  correction). A transaction that reads what the witness does not prove is undone and left out of the
  block. The undoing put back everything the transaction wrote, but a slot whose proof was missing
  had been put among the slots the engine knows, holding nothing, and stayed there; and an account
  whose proof was missing, if the transaction paid it or wrote to it, was put back as an account
  that is not there. A later transaction of the same block that read that slot or account was then
  told so, with nothing to say the witness had not proven it. If it also wrote there, the block
  failed at its end for want of the same proof (status 6) and no block came of the request; if it
  only read, a block could be built on a value the state does not have: an invalid block, bid for.
  It took a witness that lacks a proof one transaction needs and a later transaction reading the
  same place without writing it. No such block is known: every block the feeder was sent, in tests
  and live, was judged by a node (11,466 in one 1,000-slot test, 14,075 in the one
  after it, all valid), and a relay that checks blocks would have refused one. It was found by a new
  test that gives a block's missing node in a second request and has the left-out transaction tried
  again, which read the slot remembered as empty and paid for a write as if to an empty slot.
  Now a slot or account that could not be fetched is not kept, and nothing is written in a world
  already marked as having asked for what cannot be answered (`World.slot`, `setAccount`,
  `setSlot`). Checked in `build-test`: the world after such a transaction is undone holds nothing of
  the slot or the account; and each of three blocks of mainnet built with one node of its witness
  left out, for 8 nodes and both rules, is a block the checker accepts. The engine as a checker of
  blocks (`JENG1`, and the chain the machine follows) was not affected in its verdicts: there a
  block that reads what the witness lacks gets no verdict at all.
- *The loop was rewritten for it* (`Evm/Machine.lean`). Requests are run in the order they came on each
  connection, one at a time over all; a client waiting on a relay holds up only itself. While a block is
  built for a bid the network is looked at before each transaction, so frames are now read in the
  middle of that request: they are handled by the same code as at any other time, and no request is
  begun there.

**Start-up routines that do nothing.** `evm/rt/start.c` stands in for seven of mathlib's. If any code the
service reaches reads a constant one of them would have built, it reads memory nothing has written. This is
the rule "nothing that is not there may pass for something that is" broken on purpose, and the fixtures
agreeing is all that stands behind it.

**A stack with a hole under it** (2026-11-25, and in the image running on Compute Engine since
2026-11-26 15:18 UTC; before that nothing: recursion past the end wrote into the image). `evm/boot/stack.c` moves `main` to
64 MiB of the image's own memory, and the lowest 1 MiB of it is taken out of the mapping first
(`boot/efi/guard.c`, above). Recursion that uses up the other 63 MiB reaches the hole, and the machine
says its stack ran out and stops; it starts again only if whoever runs it starts it, with new keys.
So what a request could do by driving recursion deep is stop the builder, which a sender to its port
can do in other ways, and not write over the image. How deep a request can drive it has still not been
worked out. A function with a frame larger than the hole could step over it: the largest frame in the
image is under 6 KiB. `scripts/stack-check` runs a program that recurses without end on that stack:
on OVMF emulated, in a trust domain here, and on Compute Engine it stopped at the top of the hole and
said so. The firmware's own stack, which firmware's code and the OS's other images run on, has
whatever firmware gave it.

**Where the port is reachable from.** On the machine it was made on, the port is forwarded by
QEMU from the host's loopback, and whoever can reach it is on that host. On Compute Engine
(since 2026-11-24) the machine has a public address, and a firewall rule of the project's lets
one address in: the machine at home that feeds it. The rule is Google's to enforce and is no
part of what is measured; the connection is plain TCP with no proof of who is sending. So
whoever can send from that address, or stand between (the host, Google's network, the networks
on the way), can do what the host here could always do: put requests, read the answers and
every public transaction in them, have the builder build and bid, or starve it. They cannot
read a sealed transaction or sign with the builder's key, which never leave the machine, and
what the machine sends to relays goes inside TLS to names checked against the roots in the
image.

That was not all the firewall let in until 2026-11-25 18:30 UTC. The machine is on the project's
`default` network, which comes with rules of Google's making that let anyone reach every
machine on it by ICMP and on TCP 22 and 3389, and this project had one more for TCP 8080. So
for its first day and a half on a public address the guest took packets from anywhere: it
answered pings, and it answered a SYN to one of those ports with a reset, as it does for any
port but its own (`Tcp.listen`), keeping nothing. What that exposed to everybody was the code
that reads a frame, an IP header with its pieces put together, ICMP and a TCP header; not the
request port, and nothing that reads a request. Nobody looked at what came in that way, and
the guest keeps no count. Since then a second rule (`silo-test-deny-rest`, ahead of Google's)
drops everything for this machine that the feeder's rule does not allow; tried from the
feeder's address, where those three ports were refused before it and are silent after. Tried
from no other address. `scripts/gce-wall` makes both rules for a machine started from here on, and
lists every rule that can still let something reach it.

**A door for everybody else** (`evm/builder/door`, 2026-11-25; open to the public since 18:41 UTC
that day, below). The port cannot be opened to all, since whoever reaches
it can have the builder build and bid. The door is a program on the untrusted side that listens for
HTTP and passes on to the guest's port only this: the guest's two keys asked for with a report, a
report to be made a quote, and a sealed transaction. Everything else it refuses itself. When it
runs somewhere, that machine's address is let in to the port beside the feeder's, and whoever
holds that machine can then do what the feeder can. What the door adds for a stranger: they can
have the guest ask its host for a quote (a few a minute, each a tenth of a second in which the
guest does nothing else), and they can fill the 64 places the guest has for sealed transactions
(each for an hour at most, since 2026-11-25: one that names a last slot further on is dropped),
or the door's own allowance for a minute, and so keep others' out. What a sender shows the door:
their address, the time, and how long the sealed message is. The door can drop a message or
hold it back until the slot sealed inside has passed; it cannot open one. The key it serves is
believed for the quote that comes with it, which the sender checks, not for the door's word.
While a sealed transaction is kept, the feeder is told nothing of the blocks built
(`Evm/Send.lean`), so its own check of those blocks against its node is not made. With the door
open that is anybody's to bring about: a message that opens to something shaped like a
transaction is kept whether or not it could ever go in a block, for up to an hour, and another
can follow it. For as long as one is kept, what says the blocks sent are valid is the relays'
answers alone, and the feed's rule for stopping itself on an invalid block sees nothing. Seen
in the door's first hour: 33 of 1,077 bids went without the node's word, every one while a
made-up message from this project's own tests was kept. Nothing is done about it yet.

Where it runs (`scripts/gce-door`): a small Linux machine of Compute Engine on the guest's subnet,
which is no trust domain and is measured by nobody. On it Caddy, as Debian packages it, answers
HTTPS for a name made from the machine's address under `sslip.io` and passes everything to the
door on the same machine. What that brings in, all of it on the untrusted side:
- **That machine can ask the guest anything.** A firewall rule lets it reach the guest's port, and
  the port does not know the door from the feeder. Whoever takes the machine (through Caddy, the
  door, Debian, or Google, whose it is) can do what the feeder can: have blocks built and bid,
  or keep the guest busy. They get no key and can read no sealed transaction. Nobody logs in to
  it: it has no SSH key and no service account, and the firewall lets in TCP 80 and 443 and nothing
  else.
- **Three more parties stand between a sender and the door**: whoever runs `sslip.io`'s name
  servers, who could answer the name with another address; Let's Encrypt and every other
  authority browsers accept, who could certify somebody else for it; and GitHub, which serves the
  page that does the sealing and could serve another. None of them can make a quote. A sender
  who runs the checks from the repository, and not the page as served, depends on none of them
  for whose key it is; for whether the message arrives, on all of them.
- **The door's machine keeps a line for each request**: the sender's address, the time, the path.
  Never a body.

**The input.** Anyone who can reach TCP port 5005 can send a request of up to 32 MiB, which is what a block
of mainnet with its witness needs room for (the largest seen was 22 MB). `Evm/Service.lean`
reads it in Lean, with every length checked against what is left of the request; Jaune's own decoder then
reads the blocks. The C added here never looks at a byte of it: `evm/rt/names.c` passes numbers through to
Lean, and the other two files hold no data at all.

**Time and memory.** A block's time does not follow its gas: of 100 blocks of mainnet the slowest took 70
seconds in the guest for 47M gas, and another took 26 for 60M. A pairing check costs far more time for its
gas than most of what a block does, and nothing here bounds what a sender can make of that.
The machine reads no packet while an import runs, so one request holds off every other client for as long
as it takes, and a sender who wants that can have it (a block built for a bid is the one exception: the
network is looked at between its transactions, though no other request is begun). Jaune holds byte strings as lists, many bytes of heap
for each byte of input, on a heap of 512 MiB; a request that needs more stops the machine, which says so.
A request is held as the pieces it came in until it is whole and is then joined once, so for a moment it is
held twice. Eight clients may each be part way through a request, and what is held for all of them together
is kept to 40 MiB (`maxHeld` in `evm/Evm/Machine.lean`): the client whose bytes would pass that is closed. So
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
The hash is Jaune's SHA-256, the one behind the EVM's precompile, in its compression function and its
padding; the walk over the request's bytes is this package's own (`Evm.Attest.sha256`), because Jaune's
takes a list, and a request of 4.5 MB asked for with a report, as a list, was more than the heap and ended
the guest (found 2026-11-21, by the builder's own requests). Nothing proves the walk equal to Jaune's
function: `evm-test` holds it to Jaune's at every length to 300 bytes and to four of the standard's
examples, one of them a million bytes. A report still costs memory a plain answer does not, two more
copies of the request: the largest block request kept (21.7 MB), which is answered plainly, ended the
guest when asked for with a report. Nothing is secret here, so the
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
the quote the page offers for download. From a command line `scripts/tdx-standing` does fetch both, checks
Intel's signatures on them, and says where the platform, its TDX module and the quoting enclave stand
among Intel's levels; `scripts/gce-check` runs it. It is this repository's reading of Intel's rules, tested
against Intel's answers of one day (`verify/test-tdx-standing`), and not Intel's own library.

The same server has a second page, `demo/built.html`, for blocks the builder built: for each, the request
the guest was sent, its reply, the quote made of its report, and a file of what the operator says about it
(which image, which commit, whether it landed), kept by `builder/shadow` and served from one directory. The
server opens only names that are digits and one of four endings, so a visitor's path reaches no other file.
`demo/built.js` checks in the browser that the quote is for exactly that request and reply and that the
challenge is the hash of the block's parent, which is what makes the quote no older than the parent. It
does not check the builder's signature over the bid, and it cannot know whether the block is on the chain:
"landed" on the page is the operator's word, and the visitor is told to look the hash up elsewhere. A
request holds the transactions that were proposed, so publishing one publishes them; they were public
already when they were taken from the pool.

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
starts (`drawKey` in `evm/Evm/Machine.lean`), with which it signs the builder's bids (`evm/Evm/Bid.lean`). It is
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

*How long it may take.* A request for a bid (`JBID2`) names the milliseconds it allows for transactions,
and this is the first place the machine's clock decides anything about an answer. The time is counted from
when the whole request has arrived; before each transaction the clock is read, and once the time is up
everything still proposed is left out and the block is ended with what is in it. So the block is no longer
a function of the request alone: which transactions went in can differ from one run to the next. What is
said of the block is unchanged, because a block ended early goes through the same end as any other (the
checks of what was read and made, the state root, Jaune's checks of the header) and the reply names what
went in. The sender gains nothing it did not have: it could always get a smaller block by proposing less.
Nor does whoever controls the clock, which is the processor's counter as the firmware's delay calibrated
it at start, and which goes on counting while the host keeps the guest from running: they can make a block
smaller or empty, as they can refuse to carry the request at all. The limit is looked at between
transactions only, so one slow transaction still takes as long as it takes, and with no limit named the
block takes as long as its transactions do. `build-test` ends blocks before their first transaction and
half way through (three test chains, three blocks of mainnet) and puts each to the checker; `bls-test`
does the same for a bid; in the TDX guest four slots' pending transactions with one millisecond allowed
came back as four empty blocks, signed, that the node's validator judged valid.

*A bid that was sent.* On 2026-11-21 one bid went to four relays and its block is on mainnet (26463293).
What that shows and what it does not: the relays' simulation and the chain accepted a block whose
transactions were ordered and run in the guest and a bid the guest's key signed, and the quote kept with it
says a trust domain with the quoted measurements gave that reply, the builder's key and signature in it,
to that request after the block's parent existed. It won because of a payment to the proposer of 0.02 ETH,
against 0.0076 for the next bid: that payment is a transaction signed on the host, by a wallet key in a
file on the host, which the guest was handed like any other pending transaction. So money, and the secret
that moves it, are outside the trust domain, and the host could have signed that payment for any block.
The payment's own code binds it to one block number and one fee recipient, and every payment of a run
carries one nonce, so the copies the relays were sent can cost the wallet no more than one payment; a
relay that passed one to another builder for the same slot could still have had it paid without this
block. Which transactions were offered, the proofs, the assembling of the payload, the posting, and the
making of the quote are the host's as before. The relays learned this machine's address and the builder's
key; the chain shows the wallet's address.

*Anybody can slow it with a transaction* (seen 2026-11-25). The guest runs what is pending in public,
and some of what the EVM offers costs it far more time than the gas pays for: a call to the point
evaluation precompile (0x0a) takes it seconds, because that arithmetic is Jaune's on whole numbers of any
size, and the BLS12-381 precompiles (0x0b to 0x11) are the same. The guest looks at its clock between
transactions and not inside one. So one pending transaction that anybody may send, costing its sender
50,000 gas only if it lands, kept this builder from bidding for the slots it was pending in; it need
not be sent with that in mind, and the one that did it was a rollup's. The feeder now leaves such
transactions out before the guest sees them, which is the untrusted side protecting the trusted one
from the public: a feeder that does not, or a sealed transaction that calls one, still holds the guest
for as long as the call takes. Nothing secret is at stake in this, only whether the builder bids.

It is wider than those two kinds of contract, and the guest now stands in the way itself (2026-11-25;
`Bridge.work`, `Build.txWork`; in the image after `e3faec94…`, which runs on Compute Engine since 17:09
UTC that day). Measured
on the guest's runtime (`precompile-time`), one transaction of all the gas a transaction may have, spent
on nothing but recovering signers, adding points of bn254 or raising small numbers to powers, holds the
builder four to six seconds: those contracts are priced for machine code and are Jaune's arithmetic here.
A block built against a clock now gives each transaction a quarter of a second of such work, counted
before each call from a table of what the calls were measured to cost. A transaction that asks for more
has that call fail without being run and is left out of the block, as one that the witness could not
answer for is. So a transaction costs the builder at most that quarter second a round, where it cost the
round; the point evaluation and the BLS12-381 pairing cost more than the whole allowance and are never
run in a block being built. What is left: the table is an estimate, made on one machine; work outside
these contracts is bounded only by gas (hashing megabytes, say, which was not measured); a transaction
whose proof-checking is honest and heavy is left out with the rest; and many such transactions from many
senders each take their quarter second, every round, since the feeder does not yet learn which they
were. A block being judged, as when the guest follows the chain, has no such limit: its transactions
are in it.

*A payment a person asks for, on a feed that is always running* (`builder/shadow --button`,
`builder/press`, 2026-11-25; its rule tested, blocks built with it against the test relay only, none
sent to a relay of the network yet; since 2026-11-27 a block's payment is signed once and the same bytes
proposed in every round for that block, held in the feeding program's memory meanwhile). Until now a wallet's
key was read by a run started for one payment, which ended when it was made. With the button the program
that feeds the guest hour after hour reads the key when each run starts and holds it, so whoever can run
code as that user on the feeding machine, or write the file of presses, can have payments signed for as
long as the feed runs. What stands in the way is only this: the program signs nothing without a press in
the file; it judges every press again for every block (0.01 ETH at most, 300 slots at most, 0.05 ETH in
24 hours over presses the wallet has paid for or may yet, and only while the wallet's count of
transactions is what it was at the press, so a press pays once); and each payment is good in one slot
for one proposer, as before. Those limits are lines of Python on the untrusted side, and somebody who can
change the file can as well read the key and need no press. So what is at stake is what the wallet holds,
and the wallet is to hold little. A payment still wins the slot for whatever block the host has the guest
build: the guest does not know a payment from any other transaction, and nothing here ties a press to a
sealed transaction being in the block. A leaked copy of a payment costs its gas in another block and
uses up the press. The feed is not given a key unless it is started with `--button`.

*Time.* The rule is the OS's: a secret never passes through `Nat` or `Int`, and decides no branch, no
address and no division. Jaune's own BLS code is on `Nat` and is not used on the key. `evm/Evm/Sign/` holds
field elements as fifteen 26-bit limbs in machine words; where a value decides something, both answers are
computed and `Secret.select` (checked in `Mini/Constant.lean`) picks one; points are added by one formula
that is right in every case, so nothing asks which case it is in; and the multiplication does a doubling
and an addition for each of 255 bits whatever they are. (From `03394a79…`, the image after `b1f0683b…`: four doublings, by a formula of their own that is as complete, and one addition for each
four bits of the key, of one of sixteen multiples of the point worked out beforehand. Every one of the
sixteen is gone through each time and kept or passed over by `Secret.select`, on a truth value made
from the four bits by exclusive-or, negation and a shift, so the bits index nothing and decide no
branch (`Scalar.is`, `Point.mul` in `evm/Evm/Sign/Curve.lean`). That was read in the C Lean's compiler
wrote for it, where the only branches are on the position in the key and on which multiple is being
passed, both public; `scripts/check-secret-code` looks at the field arithmetic under it and not at
this. The four bits pass through a boxed 64-bit number on the way into the loop, as limbs of field
elements do, never a `Nat`. Half the work: 4 ms a signature where 8.) Hashing the message to a point and writing the
signature out are public. The hashing is on the same field arithmetic from `b1f0683b…`, the image after `a07875d4…`,
on (2026-11-26; `evm/Evm/Sign/Hash.lean`: the map to the curve, the isogeny and the clearing of the
cofactor, following Jaune's step for step, with the first step, SHA-256, and the constants still
`JauneConsensus`'s); until then all of it was `JauneConsensus`'s on `Nat`. Its branches are on values
worked out from the message, which is the bid and public, and the key does not come near it: the
point it returns is what the key is multiplied by. A wrong point would make a signature no relay
accepts, not one that says something else. Writing the signature out is `JauneConsensus`'s.

What holds that: for correctness, `bls-test` (54,850 field operations against `Nat`, 242 sums of points
against Jaune's in every case the formula covers, the public keys and signatures of 23 keys byte for byte
`JauneConsensus`'s, the points of 90 messages those `JauneConsensus` hashes them to, a bid's hashing against `JauneConsensus`'s and against a registration a validator
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
run in that same space on bytes the sender chose (the stack has a hole under it, above). A flaw in any of
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

**Two keys are held**, the signing key above and the sealing key, and for a few slots the transactions
sealed to the second. Everything but the keys' own arithmetic is on `Nat` or on code that branches on its
values, takes time that depends on them, and must never be given a key: that is the reason the keys'
arithmetic was written apart from Jaune's. The sealed transactions do go through that code, as any
transaction does, and what that can give away of them is said under "A second secret".
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
