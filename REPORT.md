# A block builder in a trust domain, with far less inside it

A report on [`evm/`](evm/README.md), for people who build Ethereum blocks in trusted execution
environments. Written 2026-11-24 and revised on the 25th, 26th, 27th and 28th. The runs the numbers come from are recorded in
[TODO.md](TODO.md), most with their commands; some figures were counted from the runs' own records for
this report and stand nowhere else. Those records are files on the machine that made them and are not
published; the programs that count them are (`evm/builder/tools/`), and so are the keys every bid was signed with (under "Check it yourself"). What is weak is said here in short. It is said at length in the part of
[THREAT_MODEL.md](THREAT_MODEL.md) headed "The EVM service", which is kept as a dated record and is
right where the two differ; the rest of that file is about the same OS on other machines.

## The claim

A builder in a TEE asks whoever sends it transactions to trust what is inside the TEE. Where a builder
has said what that is, it is a Linux image: a kernel, an init system, a C library, a TLS
library, an execution client, the builder, and whatever configures them at boot. BuilderNet's nodes, for
one, were described in [its release notes of April 2025][bn] as full Linux TDX images holding rbuilder,
Reth, a proxy for order flow and one for attestation (what it runs in November 2026 was not looked up
for this report). The kernel, and anything that runs with its
rights, can read the transactions.

This is a builder whose guest is one EFI program of 4.2 MB. Above the firmware there is nothing else:
no kernel, no C library, no OpenSSL, no shell, no file system, and one listening TCP port. The network
card's driver, Ethernet, IP, TCP, DNS, TLS 1.3, X.509, HTTP, the EVM, the Merkle-Patricia trie, BLS
signing, SSZ and the builder itself are Lean in that one program. Lean is a language in which a
program cannot reach memory it was not given: there is no arithmetic on addresses, and an index is
checked when it is used or was shown in range to the compiler; that holds as far as the compiler
and the C under the program are right. It is all "Lean" means here: it does not mean proved, and
nothing proved covers the builder. The 0.8% of the image that is C parses no
frame, no request and no certificate. (Compiled Lean also carries small functions of Lean's own C
header inside it, which count references and reach into objects. They are counted here as Lean, and by
instructions they are most of the compiled code: the figure is under what is inside, below.)

What is claimed is narrow. It is about what is inside the trust domain, and so can read a transaction
there: one program of this size and kind, and not a Linux image. It is not a claim that someone who
sends this builder a sealed transaction has less to trust in all. The machine that feeds the guest is
outside it and measured by nobody, and it chooses every other transaction of every block: it can put
its own before and after a sealed one as often as it likes, and what it can learn about a sealed
transaction that way nobody has tested. Until someone other than the feeder has, read "less inside"
here, and not "less to trust".

It runs today in a TDX trust domain on Google Cloud, builds a block about three times a second from the public
pool while it has a block to build on (about twenty blocks a slot), signs its bids with a key drawn inside the trust domain, and posts them itself to Flashbots,
Ultrasound, Aestus and Titan. Anyone can follow one of those bids from a relay's public list (three of the four gave one when
asked) back to the source it was built from; how is below, with where that is thinner than it looks. (It did not bid from 06:40 to 15:03 UTC on 2026-11-26:
the feeder had stopped itself, for refusals that are said in the record at the end.)

Four things it is not. It is not a competitive builder: it sees only the public pool, and its blocks
were worth a fifth to two fifths of the winning ones at the median, and as little as a twentieth
summed (eleven measurements, below). It guards nothing private yet: the instance that is running holds a key for
signing bids, which guards no money, and though anybody can send it a sealed transaction since
2026-11-25 (through a door described below), nobody outside has. And it is not the same shape as a builder with its node inside: here the node is outside
the trust domain and hands the guest transactions with proofs of the state they touch. That is what lets
the inside be small. It also means the machine that feeds it, which nobody measures, sees the public
flow and chooses what the builder sees of it. Private flow has to be sealed to the guest, which is
shown here for single transactions that this project sent to itself. Sealing hides a transaction's
bytes from that machine and not what it does, which is the limit of the claim said above. The relays are sent every block whole, as any builder's relays are. So the 4.2 MB is the size of a
builder that does not yet do a winning builder's work. And it is not old or reviewed: the repository's
first commit is of 2026-11-16, the network stack, TLS and signing in it were written in the days since,
and nobody outside the project has read any of it.

Words used below. The *guest* is the program in the trust domain. The *host* is the machine it runs on
and whoever runs that: on Google Cloud, Google. The *feeder* is another machine, ours, with an ordinary
node; it sends the guest transactions and proofs over the internet. The *feed* is the feeder's program
as it runs all day against the guest on Google Cloud. A *round* is one request of the
feeder's and the block the guest builds and sends for it; a slot has several. A *head* is the chain's
newest block, and its first round is the first for the slot after it. A *witness* is the proofs a
request carries. A transaction is *sealed*
when it is encrypted to a key the guest drew (HPKE as RFC 9180 has it, to an X25519 key), so that the feeder carries it without reading it. The
*door* is a program of ours on a second ordinary machine, through which anybody can ask the guest for
its keys with a quote and hand it a sealed transaction, and nothing else. The
*test relay* is a small program of ours that takes whatever it is sent, as a relay would, and writes it
down.

## What is inside

The image as it runs on Google Cloud, counted from the linker's map and the file
(`scripts/image-inventory`):

| Part | Bytes | Share | Whose |
|---|---:|---:|---|
| The builder: engine, trie, TLS, bids, relays | 1,541,929 | 37.8% | this project's Lean |
| Lean's own library | 1,322,746 | 32.4% | Lean's |
| What is left of Jaune, an executable specification of the EVM in Lean | 757,633 | 18.6% | a third party's ([skbaek/jaune][jaune]), in a fork with changes made here |
| The OS: card drivers, Ethernet to TCP, DNS | 365,488 | 9.0% | this project's Lean |
| Start-up and constants of compiled modules, relocations, and 1,093 bytes of two libraries (batteries, mathlib) | 62,329 | 1.5% | the compiler's, the linker's, those libraries' |
| C | 31,616 | 0.8% | 2,875 lines printed at build time from programs kept as data in Lean (`Mini/`), 1,483 by hand |
| Counted | 4,081,741 | | shares are of this; the file is 4,160,512 bytes, the rest its headers, the linker's own tables and padding |

About 15,000 lines of Lean written here are in it (67 modules, 15,761 lines with their comments): the
OS's network and drivers, the builder, the execution engine, TLS and its cryptography. The C is the
allocator and reference counting that compiled Lean stands on, the entry from firmware, the primitives
the drivers call to reach a device's registers and memory, the TDX calls for a report and a quote, and
the hole under the stack (below). It moves bytes and addresses that come from firmware and from devices;
it interprets none that come over the network. Lean's own runtime, which is C++ with a library for
big numbers, is not in the image: what compiled Lean stands on here was written for it, big-number
arithmetic and the rules of UTF-8 in Lean (`Runtime/`), the allocator, reference counting, arrays
and strings as programs in a small language that are printed as C (`Mini/`), and the rest by hand.
"Lean's own library" in the table is Lean's standard library, which comes compiled.

What that count leaves out or flatters:

- **Firmware is not in it**, and stays underneath the whole time. The firmware built from source where
  this was developed is a file of 4 MB, as large as the image, of compressed C; Google's cannot be
  looked into. See the next section.
- **No Linux image was measured for comparison**; one published size was looked up. The image of
  [BuilderNet v1.6][bn16] (December 2025, the last release with public notes) for TDX on Azure is a
  disk image of 326,107,648 bytes, which its notes say holds rbuilder, Reth, Lighthouse, FlowProxy,
  HAProxy, a proxy for attestation, an operator API and acme.sh on a Yocto Linux. That is 78 times
  the 4.2 MB here, and the two are not the same kind of thing: the file was not downloaded or looked
  into, a disk image has room in it that is not code, and theirs holds two clients that follow the
  chain inside the trust domain, where this builder is shown proofs against a header it is given
  (see what the feeder can still do, below). And a Linux guest all but leaves the firmware behind once
  its kernel has started, where this program never does (next section). "Far less" is a claim about
  how much has to be right for a transaction to stay unread, a kernel and all that runs with its
  rights against one program, and a ratio of two files' sizes does not measure that.
- **Jaune is someone else's code, a fifth of the image, and still does part of the work.** The
  interpreter that runs transactions was written here and is held to Jaune by tests; Jaune's own
  interpreter went out of the image on 2026-11-25 (the image was 4.9 MB with it, and a request could
  ask for a block built by it), and a request for it is now refused. Decoding blocks, headers and
  transactions, recovering senders, checking the header, the precompiled contracts with their curves and
  hashes, and the trie of withdrawals are still Jaune's. (The receipts' trie was Jaune's until the
  image of 23:53 UTC on 2026-11-26, and the transactions' is still, for a request that does not say
  its block may go on from the one before; the feed's say so in every round but the first after
  the guest has let go of what it kept.) The fork used
  differs from upstream: in three places by code that nothing proves equal to the specification, and in
  one where the compiled code differs from the definition on purpose. Nobody here has reviewed Jaune
  itself.
- **The compilers are trusted**: Lean's, and the C compiler and linker behind it.
- **What is C is told by the file it was compiled from.** Compiled Lean is C that Lean's compiler wrote,
  built against Lean's own header, and the small functions of that header that end up inside it
  (counting references, reading a field) are counted as Lean. **They are most of it.** Of the 2,668,924
  bytes of code compiled here from Lean (this project's and Jaune's, 95 modules), 1,899,398, or 71%, are
  instructions whose source line is in that header; 307,153 (12%) have a line of the C the compiler
  wrote for the module, and 462,373 (17%) have no line. Half of the header's share is counting
  references. (`evm/scripts/header-share`, which compiles the same C again with line numbers in it: 8 of
  3,537 functions came out another size that way, 14 bytes between them. It counts code by the file it
  was compiled from, where the table above counts code and data by name and sets the modules' start-up
  code apart, so its total is not the sum of three rows there. Lean's own library comes compiled and
  was not looked into.) So the rows above for this project's Lean and for Jaune say whose
  program the bytes carry out, not who wrote the instructions: seven in ten of those are from 3,590
  lines of C by Lean's authors, trusted here as the compiler is and reviewed by nobody here.
- **Under the Lean, one thing is not sound, and one was until the image of 15:19 UTC on
  2026-11-26.** Seven of mathlib's
  start-up routines, which Jaune's modules draw in for the sake of proofs, are replaced by ones that
  do nothing: code that read a constant one of them would have built would read memory nothing has
  written, and that the test suites pass is all that stands behind it. The program runs on a stack
  of 64 MiB, and until that image nothing lay below it: recursion past the end wrote
  into the image. Now the lowest 1 MiB is taken out of the page tables before anything runs on it,
  and a stack that runs out stops the machine with a line saying so. That is 199 lines of C written
  by hand, which copy firmware's tables and change them; a program that recurses without end was
  stopped by it emulated, in a trust domain where this is developed, and on Google Cloud. How deep
  a hostile request can drive the recursion has still not been worked out: what it can do now is
  stop the builder, and it starts again only when someone starts it, with new keys.
- **Nothing keeps the image's code from being written or its data from being run.** But for that
  megabyte under the stack, every page is as the firmware mapped it, and nothing here sets code
  apart from data. So a fault in the runtime's C, in the compiler, or in the firmware's own code is not
  contained by the processor's page rights as it would be under an ordinary kernel. Lean's own
  checks are what stand in the way, for the Lean.
- **Nothing proved covers the builder.** Parts of the runtime have proofs: about its big-number
  arithmetic, its reading of UTF-8 and its allocator (`Proofs.lean` gathers them). The network stack and the
  builder are tested: the cryptography against OpenSSL's, the engine against Ethereum's own suites
  (4,723 files) and against Jaune, the blocks against reth's validator. That is evidence, not proof.
  The repository's CI builds the image, tests the tools around it and, since 2026-11-26, builds the
  builder's Lean and runs its own tests (the engine's parts against Jaune's, blocks checked and built
  on the fixtures, the pairings, TLS). Ethereum's suites, the image in a trust domain and the runs of
  slots are run by hand where this is developed. The suites were not run again for every image; they
  were for the one that runs now, on the source it was built from (2026-11-27: all 4,723 files pass).
  The TLS and the cryptography under it were written here and have been read by nobody who writes such
  code for a living.

## What a relying party trusts

On Google Cloud:

1. **Intel**: the processor, the TDX module, the quoting enclave. The processor's `RDRAND` is the
   only source of randomness the keys are drawn from.
2. **Google's firmware.** It starts the guest and is never left: it owns the page tables and
   exceptions for as long as the program runs, shares its address space, and could read its keys. It
   is measured (MRTD), and Google signs a statement for that measurement, which is checked. What it
   does is Google's word; nobody else builds it. On a machine of one's own the firmware can be built
   from source, as it is where this was developed, and making it small would be the next reduction.
   What the program still asks of it once the card is up is three things: to print a line on the
   console, one for each request served (its status, how long it took and in what parts, how much
   went to how many relays and what each answered; for a block that sealed transactions were tried
   in, not its size, the parts of its time, or whether they went in); a counted delay of a millisecond when nothing has come from
   the network for a while; and, once a second, to read two registers of the card, which say whether
   the card has started over. Packets, the time and the request for a quote do not go through it,
   and its timer is stopped when the program starts, so that its code runs when called or when the
   processor raises an exception, and not otherwise (`THREAT_MODEL.md` has each of these). That is
   on Google's card; on the virtio card of a machine of one's own, each time the card is told there
   is work for it goes through the firmware as well. None of it makes the firmware less trusted:
   it is in the same address space the whole time.
3. **The image**, measured into RTMR1 together with the partition table of the disk it starts from.
   Anyone can work that value out from the image's file.
4. **Four certificate roots** the image holds for the relays' names, and every authority under them.
5. **What built the image**: Lean's compiler, the C compiler and linker that come with it, and the
   ready-made modules of mathlib it is linked against. That the image came out the same file on the two machines it
   has been built on says the build can be repeated, and nothing about those.

Not trusted, and what it can still do: the host (but for its firmware, above), the cloud's network, and
the feeder. The feeder runs an ordinary node and hands the guest pending transactions, the parent
block's header and proofs of the state they touch; the guest checks every proof against the state root
in that header. The header itself is the feeder's word: the guest does not know what the chain's head
is.

- The feeder can starve the builder, choose what it sees of the public pool, and add transactions of
  its own.
- It names the slot, the proposer, the fee recipient, the time, the randomness and the withdrawals,
  and the guest signs a bid for whatever it then builds, as often as it is asked. A block built on
  inputs that are not the chain's is for a relay to refuse.
- No request has the guest sign anything but a bid for a block it has just built, and none returns the
  key. That is as good as the code that reads the feeder's bytes: a fault there that let memory be read
  would give the key up, and what is known to be unsound is said above and under side channels.
- It does not see a transaction sealed to the guest, and can still learn much about one.
  - Unless the sender brings the proofs, the feeder is asked for them and so learns which accounts and
    storage the transaction touches.
  - The relays publish each bid's gas, value and count of transactions, so the feeder can tell whether
    a sealed transaction went in and what it paid.
  - A feeder that works at it can find out what the transaction does without reading it. It chooses
    the other transactions of the block and may write them. One of its own put before the sealed one
    sets the state the sealed one runs in; one put after reads what the sealed one changed; the
    relay's figures say how each fared. A few such blocks over a few slots can show which contract
    it touched and which way and how far it moved a price, which is most of what a trade is hidden
    for. No rule about order mends this (THREAT_MODEL.md has the ones thought through). None of this
    asking has been tried here.
  - What sealing still keeps from such a feeder: the bytes and the signature, until the block is in
    the chain, and the sender unless the feeder is asked for the proofs, since the sender's account
    is then one of those it is asked to prove; and the transaction cannot be changed, or built in
    after the last slot its sender named.
  - What the guest answers the feeder for a block it tried a sealed transaction in: no header, no
    hash, no value, no count, and not whether the transaction went in; what each relay said; and,
    for a transaction sealed without proofs, which accounts and storage slots it read that the
    request did not prove. The feeder also sees how long the round took.
  - A transaction sealed without proofs is run on whatever state the feeder proves, against a
    header that is the feeder's word. So a feeder can have it run on a state it made up, send the
    block nowhere, and see what the transaction reads there. One sealed with its own proofs is run
    only on a block the guest has itself checked to follow from its parent by the EVM's rules, and
    is not answered for in that way. The guest on Google Cloud is not shown the chain's blocks by
    the feed that runs today, so there such a transaction is kept and never built in: that path
    has run only on one machine here (the third block under what it does).
- The relays are not in that list of the trusted, and read everything all the same: the guest posts
  each whole block to them, a sealed transaction in it with the rest, before any proposer has signed
  for it. That is so of every builder that bids through relays, and it is not mended here.
- The feeder also tells the guest the date, and the relays' certificates are judged at that date: a
  feeder with an expired certificate of a relay's and its key could have it accepted.

**Set beside a builder with its node inside**, for somebody deciding where to send a transaction:

- The same in kind. Both ask the sender to trust a measured image, the firmware under it and Intel.
  Both are reached over a network their host controls, and either can be starved by it.
- Less to trust here. What can read the transaction inside the trust domain is the firmware and one
  program whose parts are listed above, that
  builds to the same file in minutes and can be checked against the running guest's quote. (It has been
  built on two machines, this project's and one of GitHub's; nobody outside has done it.) It has
  one port, no shell and no operator's interface, and takes nothing from outside when it starts but
  which of two network cards it finds: to change what it does is to run another image, with another
  measurement.
- More to trust here. A builder with its node inside puts a block together from a pool that many
  feed, in an order of its own; its host can add transactions to that pool and cannot place them.
  Here one machine outside chooses every other transaction of the block and may write them, which is
  what makes the asking described above cheap. And that builder follows the chain itself, where this
  one is told what the head is.
- So nothing here is new in kind. The claim is one of amount: how much has to be right for a
  transaction to stay unread, against a price paid in what the machine outside can find out by
  asking. Which of the two weighs more for a given sender is not for this report to say, and the
  second has not been measured.

## What it does

Each slot the guest is handed pending transactions and proofs, builds a block, signs the bid with a BLS
key drawn inside the guest, and posts block and bid to the relays over TLS connections of its own. It
does that again about three times a second until about half a second after the slot has begun, each
time with what has arrived since. (Until 02:14 UTC on 2026-11-27 the answer to a slot's last bid was
due 0.7 s before the slot. In the half hour looked at, the bids that proposers took had reached their
relays about a second into the slot, as the numbers say below, and a relay takes bids until it has
handed a block over.) (A round took about a second until 2026-11-26, three quarters of one on the image of 15:19 UTC
that day and half of one on the image of 19:15.)

Since the image of 23:53 UTC on 2026-11-26 a round goes on from the block the round before built. The
guest keeps that block as it stood after its last transaction, with the engine's state and what the
state root was worked out with, and when the next request is for the same block and proposes the same
transactions and more, it runs only the new ones, after those already in. A round that goes on cannot
come out with less than the one before it. A block that has passed half the gas a block may use is
built from nothing again, in order of what each transaction pays, and so is a block the guest adds a
sealed transaction to: nothing worked out from a sealed transaction is kept.

Since the image of 15:19 UTC on 2026-11-26 the guest keeps what a request to build gave it: the proofs' trie nodes,
contract codes and headers, up to 16 MiB and then none of them, and who signed each transaction of the
last request. A round is then sent only what is new: of the bytes that the same rounds would have carried whole, 6%
in the 1,000 slots the image that runs now was tried with. Until then it
carried nothing from one request to build to the next but its keys, its connections and the sealed
transactions. Nothing kept is taken on trust: a node or a code is found by its hash as one in the
request is, the headers are checked to be a chain when they are given and kept as checked, and a signer is used only for the
very signature it was worked out from. What does change is that a block now depends on the requests
before it as well as its own, all of them the feeder's. [THREAT_MODEL.md](THREAT_MODEL.md) has the
rest.

What the feeder does today, since none of it is in the image and all of it shapes the numbers. It
proposes up to 400 pending transactions, best paying first; none is left out for whose it is. It
leaves out transactions that carry blobs, and those that call the point-evaluation and BLS12-381
precompiled contracts, which the guest runs too slowly; it holds back a transaction that touches
very many accounts or storage slots until a round has time for its proofs. A relay that answers 500
or more is left alone for ten minutes and longer; one that answers 429 is posted to no more often
than every 1.3 s; one that refuses a block for an address on its list, or because the slot's
proposer has not named this builder, is sent no more on that head, and the blocks still go to the
others. (Flashbots' relay and Titan's refuse blocks that touch listed addresses: 126 such refusals
in thirteen hours, in the record at the end.) And the feed stops itself, for a person to look,
when more than one answer in twenty over fifty slots is a refusal or more than one block in twenty
is not judged valid by its node.

Three blocks built in the guest are on mainnet. One (26463293) was built from the public pool. Two
(26465583, 26470277) each hold a transaction that was sealed to the guest and that the feeder carried
without seeing. All three won because a test wallet paid the proposer 0.02 ETH, in a transaction the
feeder signed and proposed with the rest; the guest signs no payment. In both sealed cases the sender and the feeder were one program on one
machine, so they show that the parts fit and nothing about an adversary. They were built on one machine
here, where host and feeder are the same machine, by the images of 2026-11-21 and 22.

A fourth was built in the trust domain on Google Cloud, by the image now running, and proposed: block
26513991, slot 15754002, 13:20:47 UTC on 2026-11-28, hash
`0x584d6d7822c32cdd7fa383f254038426fcc3c643565ec28edee3d3a8269ed0b2`, extra data `cluck`. It holds
107 transactions and used 45.7 million gas. Flashbots' relay and Titan's list it as delivered under
the builder key `0x96b099d9…928e3604`, the key in the table under "Check it yourself" and the one
the running guest's quote names. It was taken because it was paid for, like the three before it. The
owner told the feeder to add 0.01 ETH to the bids of five slots (the button `THREAT_MODEL.md`
describes), and the first of the five was taken: the bid was 0.01176 ETH, of which 0.01 was that
payment, the block's first transaction, signed by the feeder with the test wallet's key and proposed
with the rest from the public pool. The guest signs no payment and does not know one from any other
transaction. Without it the block was worth 0.00176 ETH, and the highest bid not ours that Titan's
list holds for the slot was 0.00422 ETH. The slot was one of the few where the guest starts over on
a large block: three rounds and not twenty-five, the last answered 0.42 s before the slot began and
at Flashbots' relay 1.03 s before it. The next four slots' bids carried no payment, and the feed went
on as before. What this shows: a block built in that guest, on that cloud, is one that relays hand on
and a proposer signs, and it is valid on the chain. What it does not show: that such a block wins
unpaid. No sealed transaction was in it.

## Numbers

**What runs now, and the record whole.** The image described above has bid since 23:53 UTC on
2026-11-26, and since 02:14 on the 27th its rounds go on into the slot; the list after this paragraph
has its numbers, a day of them among them. All
the images together, from 18:30 UTC on 2026-11-24 to 23:48 on the 26th: 15,991 slots went by and a bid
was sent in 13,028. Of the 2,963 without, 2,706 have no record (the feed was stopped, 2,515 of them
from 06:40 to 15:03 on the 26th, or an image was being changed), in 201 no relay held a
registration, in 54 a block was built and nothing sent, and in two nothing was built. 83,410 blocks
were sent: 83,377 were judged valid afterwards and 33 could not be judged (the guest showed the
feeder no block then; the last section says why); none was judged invalid. The relays gave 262,063 answers: 189,992 of
200, 71,707 of 202, 166 refusals of 400, 75 of 429, 68 of 500 or more, and 55 posts had no answer.
No proposer took a block in that record: the three blocks on mainnet (under what it does) are of the
days before it, built on one machine here and paid for. That record is taken image by image in the last section of this report;
its numbers are of images that no longer run.

**The image that runs**, on Google Cloud (`c3-standard-4` with TDX, us-central1, about 23 cents an
hour), fed over the internet from a node 12 ms away, bidding at four relays with nothing paid for a
win:

- **Its first hour there**, from 23:53 UTC on the 26th: 300
  slots went by and a bid was sent in 295, 98.3%; in the other five no relay held a registration
  from the proposer, and no slot was built for with nothing sent. 5,795 blocks built and 5,166
  sent, every one judged valid afterwards; 5,388 of the rounds went on from the block before. No
  round ended after its slot began, and none had nothing in it. 19 rounds a slot, 0.34 s a round
  (one in ten over 0.62 s) and the last bid 0.80 s before the slot, at the median. Of 14,339
  answers 13,174 were 200 and 1,164 were 202 (a 202 says the bid was under the relay's floor and
  the block was not checked; that a 200 means the relay ran the block rests on a few rows of two
  relays' lists that were looked at, as the record at the end says, so "valid" in this report is
  the feeder's own node's verdict); one was 429 ("too many requests"), in the first
  minute, and that relay has been posted to less often since, in 2,373 of the rounds.
- **The first hour with its rounds going on into the slot**, from 02:14 UTC on the 27th: 300 slots
  and a bid sent in 294; five had no registration and one was the slot the feed began in. 6,569
  blocks built and 6,082 sent, every one judged valid afterwards. 284 rounds ended after their
  slot began, as they are now meant to, in 283 slots; 22 rounds a slot, and the answer to the last
  bid was back 0.55 s after the slot began, at the median. Of 16,932 answers 15,356 were 200 and
  1,574 were 202, one was 429 and one post had no answer; no relay refused a block for coming
  late.
- **What relays say to a bid that comes after the slot began**, 02:14 to 05:19 UTC on the 27th:
  889 rounds had their answers back after their slot began, most by 0.5 to 0.7 s and twelve by
  1 to 1.9 s, and of the 2,828 answers to them 2,823 were 200 or 202, two posts had no answer,
  and three were 400. Two of the three were for something else (an address a relay keeps a list
  of, and a proposer who takes blocks only from builders it names). One was for coming late: in
  slot 15744140 a bid whose answers were back 0.68 s after the slot began was told "submitted
  block is for past slot" by Ultrasound's relay and taken by the other three. The feeder sends
  no more for a slot once a relay says so. So in three hours no relay refused by the clock.
  (The next came at 09:46: Titan's relay, "late sim, already on next slot", to a bid whose
  answers were back 1.35 s after its slot began.)
- **A day of that**, 02:14 UTC on the 27th to 02:51 on the 28th, 24.6 hours in 25 runs of the
  feed (`builder/tools/day.py`): 7,384 slots went by and a bid was sent in 7,277, 98.6%. In 106
  no relay held a registration from the proposer, and one was the slot the feed first began in;
  none has no record. 174,950 blocks built, 166,271 of them going on from the block before, and
  160,542 sent, every one judged valid afterwards. 24 rounds a slot, 0.35 s a round (one in ten
  over 0.58 s), and the answer to the slot's last bid back 0.54 s after the slot began, at the
  median. Of 438,503 answers 401,107 were 200 and 37,267 were 202; 82 were refusals and 47 posts
  had no answer. The refusals: 25 of 429 ("too many requests"); 23 "builder not in proposer's trusted
  list" and five "blacklisted address", which are about the proposer and the block; 13 that
  said the slot was past; four "payload attributes not (yet) known" and two "could not find
  parent block"; ten of 500 or more. The 13 are all the refusals for coming late in the day:
  eight from Titan's relay, each to a bid whose answers were back 1.3 s or more after its slot
  began, and five from two other relays at 0.42 to 0.68 s, in four slots. Of the 912 rounds
  whose answers were back 0.7 to 1 s after the slot began none was refused so. In three slots
  besides the one the feed began in, the last round came out with nothing in it and the slot's
  bid was an earlier one; 89 slots (1.2%) had a block past half the gas cap, which the guest
  builds from nothing each round, and those had six rounds at the median. No proposer took a
  block, and nothing was paid for one. (The feeder can add a payment to the proposer to a slot's
  blocks when its owner tells it to, as `THREAT_MODEL.md` says; from 15:52 it ran able to, and
  was not told to.)
- **Before it went there, 1,000 slots where this is developed**, in a trust domain against the test relay,
  on the image's twin for that relay (the same code but for the list of relays and their
  certificates' roots, so another file with another measurement)
  (20:19 to 23:39 UTC on the 26th): a block sent in 998 slots. The two without had one round
  each, of 10.5 MB after 7 s of gathering proofs for more than 900 accounts: one block came out
  with nothing in it, and the guest kept the other back because a transaction ran it 0.6 s past
  the time the request allowed. 34,298 rounds, of which 34,294 gave a block, every one judged
  valid by the node there, and four were a head's first round with a witness that fell short and
  no block. 32,984 rounds went on from the block before. 36 rounds a slot and 0.18 s a round at
  the median, 0.05 s of it the guest's, where the image before it had 14 rounds a slot in the
  same test. One round ended after its slot began, by 1.15 s: its request was 8.7 MB and took
  the feeder 3.2 s to gather; the slot's bid before it was 2.9 s before the slot. In two more
  slots the last round came out with nothing in it, because the block had passed half a block's
  gas and was built from nothing with too little time left; the slot's earlier bid stood.
- **And 300 slots on a test machine on Google Cloud**, fed over the internet with no relay: a block
  in every slot, 3,363 of 3,364 rounds built and judged valid, 3,024 gone on. A round 0.30 s
  where the image of 15:19 took 0.89 s in the same kind of run, the feeder's wait for the guest
  0.14 s of it where 0.50. (The image of 19:15 was not run that way.)
- **The same 74 requests put to three images in a trust domain**: 240 ms a request by the
  guest's own count on the image of 15:19, 108 ms on the image of 19:15, 84 ms on this one built
  from nothing and 34 ms going on. Of the 34, at the median of each part: 1 to read the request, 12 to the last
  transaction, 13 to end the block (the state root, mostly) and 9 to sign.

**Against the blocks proposers took**, as relays' public lists give what each paid. Measured twelve
times, over up to 6,290 slots a relay listed each: ours was 18% to 45% of theirs at the median, and 4.5% to 31%
summed. Nine of them, the largest and the latest:

- From Google Cloud over a day, the rounds going on into the slot (02:14 UTC on the 27th to 02:51 on
  the 28th; 6,290 slots a relay listed of the 7,276 bid in, `builder/tools/gapday.py`): ours 45% of
  theirs at the median and 13% summed. The taken blocks paid 0.0065 ETH at the median and 166 ETH in
  all, ours 0.0028 and 21. In one slot ours was worth more, 0.00555 ETH against 0.00549, and the
  proposer took the other, through a relay this builder does not post to. With 0.005 ETH added ours
  would have been above the taken block in 66% of the slots, and with 0.01 ETH in 82%; that is
  reckoned, and no bid was made with anything added.

- From Google Cloud on the image that runs now (its first hour, from 23:53 UTC on 2026-11-26; 255
  slots a relay listed): ours 41% of theirs at the median and 30% summed; 90% at best, never more.
  The taken blocks of that hour paid 0.004 ETH at the median, which is little; one hour does not
  say that three rounds a second earn more than one did.
- The same image with the rounds going on into the slot (02:14 to 03:14 UTC on the 27th, 250 slots a relay
  listed): 32% at the median and 10% summed; 80% at best. At the median the taken blocks paid twice
  what they had two hours before and ours 1.4 times; summed, theirs 7.0 ETH where 1.5 and ours
  0.72 where 0.45, a few slots making most of theirs.
- From Google Cloud at the real relays (the hour from 04:28 UTC on 2026-11-25, 267 slots for which a
  relay listed what the proposer was paid): ours 34% of theirs at the median and 31% summed; 80% at
  best, never more.
- From Google Cloud again, on the image of 17:12 on the 25th (23:12 UTC on 2026-11-25 to 01:46 on the 26th, 651
  slots a relay listed): 32% at the median and 11% summed; 85% at best, never more.
- On one machine against the test relay (2026-11-22 and 23, three runs of 1,000 slots): 29%, 27% and 29%
  at the median; 19% and 17% summed in the first two, and the third was not summed.
- On one machine at the real relays (2026-11-24, 253 slots): 18% at the median and 4.5% summed, in an
  hour when the taken blocks were worth twice what they had been the night before.

**When the bids are made.** A relay's public list says when it received each bid. For 150 slots in a
row (01:00 to 01:30 UTC on 2026-11-27, one half hour) 130 had a block taken through a relay, and 88
of those a time for the bid that was taken (56 from Titan's list, 25 from Ultrasound's, six from
Aestus', one from Flashbots'): none had reached its relay before the slot began, three had by
0.85 s after it, and the median was 1.07 s after. That is when the relay had the bid; the proposer
asked some time after, and when is not listed. Until 02:14 that day the answer to our last bid was
due 0.7 s before the slot and came 0.8 s before it at the median, and a relay has a bid about 0.2 s
before its answer is back: so the bid was there a second before the slot, and every comparison
above but the one from 02:14 is of a block made about two seconds sooner than the one it is
measured against. Since then the last of ours that Flashbots' relay lists reached it 0.37 s after
the slot began, at the median of 57 slots looked up. What that is worth is measured inside each
slot, where the hour's prices cancel: over 283 slots of the first hour after 02:14, the slot's last
block paid 11% more, summed, than the last one that would have been sent under the old rule (8.8%
at the median; the two blocks were 1.5 s apart), and over 7,234 slots of the whole day from 02:14
12% more (9.9% at the median, a quarter of the slots under 4.8% and a quarter over 17.7%). So
going that much later is worth about a tenth. Looked up again in 86 slots of three hours of that
day (from 05:14, 13:13 and 22:52): the last of ours that Flashbots' or Ultrasound's relay lists
reached it 0.40 s after the slot began at the median, and the 45 taken bids with a time reached
their relays 1.02 s after it, four of them by 0.85 s and none before the slot.
That still ended half a second or more before most of the taken bids were in. Since 02:58 UTC on
the 28th the rounds go on 0.3 s longer. Over the ten hours that followed (a bid in 2,949 of 2,996
slots) the answer to a slot's last bid came 0.84 s after the slot began at the median, and by the
same count the last block paid 15.3% more, summed (11.8% at the median), where the same ten hours
of the day before gave 12.0% and 9.9%: about three points of the bid for 0.3 s. It bid in the same
share of slots and every block sent was judged valid. What it cost: in 26 slots a relay refused
the last block as coming after the slot was over, against three such refusals in the same hours
the day before; 22 of the 26 were rounds whose answers came 1.15 s or more after the slot began,
and the bids before them in those slots stood. In 40 slots looked up, the last of ours a relay
lists reached it 0.63 s after the slot began and the 21 taken bids with a time 1.31 s after: ours
still end before most of the taken bids are in. Later than that has not been tried.

The summed figure is the truer one: the slots that pay are far above the median, and in those ours is
furthest behind. Of what the taken blocks held that was public a second before the slot, ours held 84%
to 91% by fees summed over a run, and 89% to 94% at the median (four runs on one machine), and from
Google Cloud 86% summed and 90% at the median (600 slots from 23:50 UTC on 2026-11-25, the last block
ready 0.78 s before the slot; of what was public three seconds before, 95% and 99%). Public means in
the pool of the one node that feeds it. So most of
what it lacks was not public as that node saw it, and some of it was public and not taken. In those
600 slots the fees public by the slot's start that ours lacked came to 0.31 ETH: seven parts in ten of
it became public in the last two seconds, after the slot's last round had begun (a median 2.0 s
before the slot), and the rest was public earlier and left out. Of what was public half a second or
more before the last round began (0.06 ETH), a third carried blobs, a third was in slots whose last
round came to nothing (below, under what is not done), and a third was left out by the limits on a
round's time and size. Against that, the taken blocks of
those hours paid their proposers 13 ETH. That count stops at the slot's start, which the paragraph
above shows is a second before the taken bids were in, and what became public in that second is not
in it. With that said: of what the taken blocks paid, little was in this one node's pool for a
builder of this kind to take, sooner or later.

**How fast the parts are**, on the image that runs now. By the guest's own count, on the machine it
was developed on, a block that goes on from the one before takes it 34 ms and one built from nothing
84 ms (the same 74 requests; the images of 19:15 and 15:19 on the 26th took 108 and 240 ms over them,
and the images of the 25th about a third of a second over requests of their day). From the feeder on
Google Cloud, in the first hour: a round 0.34 s at the median, of which asking the guest is
0.21 s (the request crossing the internet, 56 kB at the median, 0.1 MB in a slot's last round and
0.3 MB in its first; the build; the posts to the relays with their answers) and the rest the
feeder's finding and tracing of transactions and fetching of their proofs. A post to four relays takes 0.07 s on
connections the guest keeps open; reth imports a block in 0.04 s.

## Check it yourself

A relay lists every bid it is sent with the key that signed it. The guest says, in a TDX quote, that
the key is its own. So a bid can be followed back to source with nothing from us but this repository:

1. **The bid.** Ask a relay for the bids under the builder's key;
   [`docs/live/builder.txt`](docs/live/builder.txt) has the key and a link. Flashbots, Ultrasound and
   Aestus list them; Titan gave no answer when asked.
2. **The key is the guest's.** `docs/live/builder.quote` is the guest's answer to "what is your key",
   quoted by the machine it runs on. <https://posix4e.github.io/cluck/live.html> checks it in a browser,
   as far as a page can: it takes the image's measurement from a file of ours.
3. **The guest is this program, on Google's firmware.** Build the image from the commit
   `docs/live/builder.txt` names, in a checkout of its own: the record is written after the commit it
   names, so the files under `docs/live` at that commit are of the guest before, and the newest
   checkout is the one to take the record, the quote and the script from (the commands are under
   "Reproduce it"). `scripts/gce-check` asks five things: that the quote's signatures lead to
   Intel's root; that Intel, asked today, calls the platform's microcode, TDX module and quoting
   enclave up to date and has withdrawn none of the certificates; that RTMR1 in the quote is what
   Google's firmware measures for that image file; that Google signed for the firmware in MRTD; and
   that the quote is of that key.
4. **The program is this source.** The image's SHA-256 is in `docs/live/builder.txt`. Built from
   nothing on a machine of GitHub's, from the commit named there, it is the same file byte for byte,
   and the guest's quote passes those questions against the file built there: the workflow is
   [`image.yml`](.github/workflows/image.yml). Anyone can see [its runs][image-runs] and whether
   each passed; GitHub shows a run's log, with the hashes in it, to whoever is signed in. It runs
   again whenever the files under `docs/live` change.

**The keys it has bid under.** A guest draws its key when it starts, so each start on Google Cloud
has had another. These are all eleven since the first bid from there, with the first and last slot
a bid under each was sent and its time (UTC, November 2026), from the feed's records by
`evm/builder/tools/keys.py`. A relay's public list of the blocks it received for a slot
(`/relay/v1/data/bidtraces/builder_blocks_received?slot=`) has rows with these in `builder_pubkey`:
looked up for one slot each of the first key, the ninth and the last, Flashbots' list had them all
and Aestus' two of the three (for the third slot it lists nothing from anyone). How long a relay keeps that list is its own affair. Only the last
key has its quote published here, so that the ten before it were a guest's is our word; what the
lists bear out is what was bid under them.

| Key | First bid | Last bid | Slots bid in |
|---|---|---|---|
| `0x85cbb82a2f9a25ff1220b164e68977cd10fbe643c3fe0828d5eb8c3ef2a47bc786e4c6d859438e3d0be39ddfe5643258` | 15726753, 11-24 18:30 | 15727166, 11-24 19:53 | 406 |
| `0x94ab682bd1c6938cb037dc5677593ec103fef1ceec5068aaa4dbba28366fa023144f15273359e21fba3558997e91ce20` | 15727192, 11-24 19:58 | 15728088, 11-24 22:57 | 885 |
| `0xb24238012deaafaabb33383829c79fa1eea5fac9f9051060ffe32f6a2d491603b7c82195fa3d6b31b0db0f748ca2f661` | 15728092, 11-24 22:58 | 15728391, 11-24 23:58 | 295 |
| `0x820f042ab980414482dd6d8421c8a975e4594c22369fdcef50351ee359412ee1be4292c424462ad4b81db47da8e09bd9` | 15728395, 11-24 23:59 | 15728993, 11-25 01:58 | 584 |
| `0x999e5d1ebf3f8fc6c5a3de2e59ed8f659b2a3adc5d83d936a24bc29d64e20ce12976948107551a3021a77e6e4b9a7703` | 15728997, 11-25 01:59 | 15729714, 11-25 04:23 | 703 |
| `0x928980a909925197c1cd07b1ebdc451c7297cb529df3382b038a88d2d9dd1c8eef5b6a2f6fe91f339a5cd7758f9ff6e8` | 15729739, 11-25 04:28 | 15732215, 11-25 12:43 | 2,427 |
| `0x894ed5e6c7a96a91cbfbb0ec8e35801e6d16ff1177f4143e89dc82010f0820e1106816b16005d808c41ba16dfd463d72` | 15732239, 11-25 12:48 | 15733526, 11-25 17:05 | 1,254 |
| `0xad9525cc5a6bb1309158387b2f018f1e9001e1eb82d21791ed94dcd06a5a3177da679e244148fc334cdfcd9111501e4f` | 15733563, 11-25 17:12 | 15740171, 11-26 15:14 | 4,012 |
| `0xac318193e0b77b32c167bbb0ae6fa37c50c29cae567ba6db18f2f6b7ec81fd38c60f197b50ed273a4bcdea55bbc7635a` | 15740197, 11-26 15:19 | 15741351, 11-26 19:10 | 1,144 |
| `0xb46fe0fe7332bf88bc9ee36536e325bf81de98508421f50eb505cadb1f33ef736da1400bc07663874f612e0ce378f826` | 15741375, 11-26 19:15 | 15742742, 11-26 23:48 | 1,311 |
| `0x96b099d9343e6b97e8bbfd3f9e9bd4f8c0791e921e679d89d855c30cb58712c0b1bb447bf84560c6ed55b970928e3604` | 15742766, 11-26 23:53 | running | |

Where this is thinner than it looks:

- The image has been built on two machines, ours and GitHub's (Ubuntu 26.04 and 24.04), with the
  same release of Lean, whose compilers do all the compiling, and the same ready-made modules of
  mathlib, fetched from mathlib's cache. Nobody here has built either of those from source.
- Intel's verdict on the platform (its TCB status, and the lists of revoked certificates) is asked
  by `scripts/tdx-standing`, written here and tested against Intel's answers of one day; it has not
  been compared with Intel's own verification library. The page in the browser does not ask at all.
  Nothing looks for a statement of Google's since withdrawn.
- RTMR0, the machine's configuration as the firmware measured it, was the same on every start seen
  and is not worked out from anything.
- The guest's port is plain TCP that asks nobody who they are. Firewall rules of Google's let in two
  senders: the feeder's address, and the machine the door below runs on. Whoever can send from either,
  or stands between, can do what the feeder can. A program stands beside the port for everybody else and passes on only requests for a
  key with its quote, and sealed transactions (`evm/builder/door`, at the address in
  `docs/live/door.json` since 2026-11-25): through it anybody can have a quote made for random bytes
  of their own, which <https://posix4e.github.io/cluck/send.html> does before it seals anything. It
  runs on an ordinary machine of Google's that is measured by nobody and could ask the guest whatever
  the feeder can; no transaction of a stranger's has come through it yet, and none has landed.
  While the guest keeps a sealed transaction it shows the feeder none of its blocks, so the feeder's
  node cannot say whether they were valid, and anybody can now bring that about for an hour a message:
  for those blocks the relays' answers are all there is. In the door's first hour that was 33 of
  1,077 bids, all while this project's own test messages were kept.
- A guest that starts again has new keys, and the record here is written by hand after a start.
  The feeder says when the two differ; until someone acts on that, the page of step 2 names a key
  the guest no longer has, as it did for more than three hours in the night of 2026-11-24.

## What is not done

- **It does not win.** No private order flow, no bundles, no blobs, nothing paid to the proposer beyond
  what the block earns. None of that is shown, and bundles and a payment signed inside would be new code
  inside; how much has not been measured.
- **Nobody has tested what the feeder can learn about a sealed transaction.** The feeder sees no
  sealed transaction's bytes. It does choose the rest of each block the transaction is tried in, as
  often as it likes, and is told of each such block what is said under what a relying party trusts.
  How much that gives away has not been tried, and the one to try it is somebody other than the
  feeder. Until then the claim is the narrow one at the top.
- **It is not fast.** One core, one block at a time, a third of a second a round. Its last bid of a
  slot reaches a relay about 0.6 s after the slot begins (0.4 s until 2026-11-28); of 88 taken
  bids looked up, 85 reached theirs later than 0.85 s after (under the numbers). The one block of
  its own that a proposer took from Google Cloud was paid for (under what it does).
- **A slot's last round can come to nothing, and the bid before it then stands.** A slot's last
  round is begun as late as will fit. On earlier images its block sometimes came out with nothing in
  it and was kept back, and the slot's last bid was then about three seconds old: in one slot of
  twenty on the image of 17:12 UTC on 2026-11-25, in one of 36 on the image of 19:15 on the 26th.
  The image that runs is sent only what it has not been and goes on from the block before: in its
  first 1,095 slots at the relays the only two such slots were ones an hour's run of the feed
  began in, and in 1,000 slots where it is developed three had such a last round. What is left of it: a block past half a block's gas, and a block with a sealed
  transaction in it, are still built from nothing every round. (How it came to this is in the
  record at the end.)
- **A full pool, or one slow transaction, has kept it from bidding, and may again.** The feeder takes
  at most 400 transactions from its node's pool, gives a round no more than fits its time, and
  leaves out transactions that call the point-evaluation and BLS12-381 precompiled contracts: that
  arithmetic is still Jaune's (the third-party EVM in Lean named under what is inside) on numbers of
  any size, and one such call cost the guest 3 s. The guest has a limit of its own as well, so that
  this does not rest on the feeder: a table says what each precompiled contract costs in time for
  its input, from measurements on the guest's runtime, and a transaction in a block being built
  gets a quarter of a second of it; a call there is none left for fails without being run and the
  transaction is left out. What that leaves: the table is an estimate, and for four BLS12-381
  contracts a guess above the ones measured; work outside precompiled contracts is bounded by gas
  alone, which was not measured against time; a transaction left out costs its quarter second again
  every round, since the feeder is not told; and transactions that need those contracts for longer
  than that are still not built in at all. (What happened, and what was tried, is in the record at
  the end.)
- **When the proposer's own account spends in the block, it does not bid.** A block's worth is counted
  as what the proposer's fee recipient holds after it over what it held before, and the block names that
  account as the one fees go to; there is no payment transaction of the guest's, and none at all in what
  runs today. In slot 15734425 (19:38 UTC on
  2026-11-25) that account sent 0.06 ETH of its own in a transaction that was in the public pool; this
  builder put it in, as it puts in any, the account ended the block with less than it began, and nine
  valid blocks of up to 72 transactions counted as paying nothing and were not sent. One slot of the 8,690
  built for from Google Cloud by then; it has not been counted since. A smaller spend would not stop a bid and would make it too low; how often
  that happened is not counted. The remedies are a payment signed inside, or leaving that account's
  transactions out; neither is done.
- **After a slot with no block it has bid once.** The feeder asked for a block only when the chain had a
  new one, so when a proposer proposed nothing this builder sat the next slot out: three slots in a
  thousand in the run here on the code of 12:47, and the same in every number before it. Since 12:28 UTC
  on 2026-11-25 the
  feeder builds for the next slot on the same parent once a slot has gone some seconds with no block.
  That was tried by pretending slots were empty (115 blocks, all valid by reth's validator), and that
  afternoon a slot stayed empty while the builder on Google Cloud was bidding (15732467): it built three
  blocks for the slot after, and all four relays answered 200 to the first two. One slot is not a rate.
  (In the run here on the image of 17:12 two slots were empty, and a block was sent for the slot after each.)
  And a block that comes late looks the same as none until it comes. The wait was four seconds at first,
  and blocks are the head at the feeder's node later than that once in 29, an epoch's first block nearly
  always: nine bids on the old parent drew the thirteen refusals said in the record at the end, in three hours. The wait is
  now seven seconds, and the feeder looks once more for a late block before it asks the guest. About one
  head in 370 is later than that, and for those a bid on the old parent can still go out, which a relay
  that has the late block refuses.
- **One feeder, at somebody's home.** When that machine or its link stops, the builder stops.
- **Side channels.** The key's field arithmetic was written to take the same steps whatever the key,
  and a script reads its machine code for conditional jumps (`evm/scripts/check-secret-code`). The
  curve arithmetic above it is not read that way, nothing was measured on a running guest, and no
  other code here had that care. Firmware shares the guest's address space.
- **The one port is not all that answers.** One TCP port listens. The guest also answers ARP, pings and IPv6
  neighbour discovery, puts fragments together, and reads DNS answers and everything the relays send.
  All of that is Lean; none of it is proved.
- **Certificates** are not checked for revocation, and the date they are judged at is the feeder's
  word.
- **Young code, all of it, and read by nobody else.** The repository's first commit is of 2026-11-16;
  `evm/` began on the 19th as a service that checks blocks, and building blocks, signing bids and the
  engine that runs the transactions are of the 21st. The TCP was
  rewritten and the driver for Google's card written in the week of these numbers. Nobody outside the
  project has reviewed any of it. The code that reads the feeder's requests and the network's bytes is
  tested on what was written for it and on what mainnet sent; none of it has been fuzzed.
- **The card is believed more than it need be.** The drivers bound what a card's answers can make them
  do, and have not been tried against a card that misbehaves on purpose. One store to a register of
  Google's card goes by the firmware's word for where the register is, with nothing to catch a wrong
  word.
- **Out of memory, the guest stops**, and a guest that starts again has new keys. Its heap is 512 MiB;
  what is held for unfinished requests is bounded, and a single request of the largest size allowed (32
  MiB) has not been tried.

## Reproduce it

What it takes: Linux on x86-64 (`scripts/build-efi` builds nowhere else) and Lean through
[elan](https://github.com/leanprover/elan), which fetches the release `lean-toolchain` names, with the C
compiler and linker used. For the check of a quote besides: `node`, `openssl`, `dosfstools`, `mtools`
and `gdisk`, and a network that reaches Intel and Google.

The image:

    git clone https://github.com/posix4e/cluck && cd cluck/evm
    # fetch mathlib's ready-made modules first: the command is in evm/README.md
    lake build
    scripts/build-efi tdx                 # .lake/build/efi/tdx/evm-os/BOOTX64.EFI

The very file that is running, and the check of step 3 above. The record names a commit older than
the one it is written in, so the image is built in a second checkout and checked from the first, which
is what `image.yml` does:

    cd cluck                                         # the newest commit: the record, the quote, the script
    git worktree add ../cluck-running COMMIT         # COMMIT as docs/live/builder.txt names it
    (cd ../cluck-running/evm && lake build && scripts/build-efi tdx)        # mathlib's modules first, as above
    scripts/gce-check ../cluck-running/evm/.lake/build/efi/tdx/evm-os/BOOTX64.EFI docs/live/builder.quote KEY CHALLENGE

with the key and the challenge as `docs/live/builder.txt` gives them in a command of its own.

On a machine with TDX, a QEMU that starts trust domains and a TDVF built from source (`TDX.md`;
`SILO_TDVF` names the firmware file, and `SILO_TDX_QGS` the socket of the machine's quoting service,
without which no quote is made):

    scripts/run-fixtures tdx --key        # starts it, asks, checks the answers

On Google Cloud, `SILO_GCE_BUCKET=BUCKET ../scripts/gce-try NAME BOOTX64.EFI` starts the same file on a
TDX machine, which costs money until it is deleted; it wants `gcloud`, signed in, and a storage bucket
for the disk. The guest takes the address 10.0.2.15 with its gateway at 10.0.2.1, so it needs a subnet of
10.0.2.0/24, a public address, and a firewall rule that lets the feeder reach TCP 5005; the script's
heading says how each is given. A project's `default` network there also lets anyone reach every machine
by ICMP and on TCP 22 and 3389, which a second rule has to close (`THREAT_MODEL.md` says what was open
here, and until when). Given a network tag in `SILO_GCE_TAGS` and the feeder's address as a range in
`SILO_GCE_FROM` (203.0.113.7/32), the script makes both rules (`../scripts/gce-wall`) and lists every
rule that can still let something reach the machine.

To feed it you need a synced reth with the `txpool`, `flashbots` and `debug` APIs and the patch in
`evm/builder/reth-state-witness.patch` (made for reth 2.11.0; its heading says how to build), and a
beacon node. The feed looks for them at `SHADOW_RPC` and `SHADOW_BEACON`, by default
`http://127.0.0.1:8545` and `http://127.0.0.1:5052`:

    builder/feed ADDRESS DIR --hold       # ADDRESS is the guest's, HOST[:PORT]. It builds every slot
                                          # and posts nothing; without --hold it bids

The scripts named in this report are at the newest commit; an older one, such as the commit a record
names, may not have them all.

## The record, image by image

What the images before the one that runs did, kept as the record of how it came to this. Nothing here
is of the image that runs unless it says so. The items are in the order they were written, which is
not strictly the order of time, and they do not add up to the whole record given under the numbers:
the hours from 15:07 to 17:05 UTC on the 25th and from 15:03 to 15:19 on the 26th, about 560 slots,
are in those totals and have no item here.

**On Google Cloud** (`c3-standard-4` with TDX, us-central1), fed over the internet from a node 12 ms
away, bidding at four relays with nothing paid for a win:

- It has bid since 2026-11-24 18:30 UTC, but for 06:40 to 15:03 on the 26th and the minutes of each
  change of image. To the image that runs that was two days and a quarter, not a long record, and
  **every number in this list is of an image that no longer runs, but where a line says "since"**.
- **All of it, to 15:04 UTC on the 25th**: 6,167 slots went by and a bid of ours was sent to a relay in
  5,973 of them, 96.9%. About half of those slots, the ones to 04:27 on the 25th, were on images of 4.9
  MB that still held Jaune's interpreter; the rest were on images of 4.0 MB. Of the 194 without: in 89 no relay held a registration from the slot's proposer,
  so there was nobody to send to; 71 were three changes of image, 23 or 24 slots each; seven were the
  three resets by Google's host (below), two or three slots each; 14 followed a slot with no block, for
  which nothing was built then (under what is not done); twelve were built and not sent, five of them in the full pool
  of 07:39 and seven with one block that paid nothing, which the guest does not send (five of
  those were the first slot after a start); and one has no record and no reason found.
  (`evm/builder/tools/day.py` counts these from the feed's records.) 30,132 bids were sent, every one judged
  valid afterwards by reth's validator on the feeder (none was left unjudged), and eight had their
  round end after the slot began. Valid there means that the block, run on the parent it names, comes
  to what its header says; it does not mean the parent was still the chain's head or the randomness the
  slot's, and nine of these blocks drew thirteen refusals from relays for those (below). In that time the guest started seven times, each time with new keys: the first start, three
  changes of image, and the three resets.
- **What the relays answered**, to all of it: 97,241 answers (a block goes only to the relays that hold
  the proposer's registration, so to fewer than four on average). 66,460 were 200 and 30,666 were 202. A
  202 says the bid was below the relay's floor and the block was not checked, so at most the 200s say a
  relay ran the block. That they do rests on little: a few rows each of Flashbots' and Ultrasound's
  public lists were looked at, and gave these bids with `optimistic_submission` false; Aestus' and
  Titan's were not looked at. 27 posts had no answer in the 1.5 s allowed.
- **What they refused**, 26 answers of 400: eight "unknown parent hash" and five on the randomness, all
  thirteen for blocks built on the old parent when a block came late, a fault of the feeder's that is
  said under what is not done; seven "builder not in proposer's trusted list", from Aestus, which is a
  proposer's choice; three "payload attributes not (yet) known" from Flashbots; one "submission for
  wrong slot"; and two, for two blocks of one slot, "block accesses blacklisted address" from Titan.
  This builder leaves no transaction out for whose it is. Before Google Cloud, on 2026-11-24, relays
  refused three blocks that paid nothing; the guest has since refused to send such a block.
- **And one relay said it could not serve.** Ultrasound's answered 503 to every post of three separate
  minutes on the 25th, 60 answers, while listing other builders' bids for the same slots; why is not
  known here. The feed, which then stopped itself when more than one answer in twenty was not a 200 or
  202, stopped at 15:04. It was started again at 15:07 with a rule that leaves such a relay alone for
  ten minutes and longer and goes on with the others; what stops it now is more than one refusal in
  twenty answers (an answer of 500 or more is not counted one) or more than one block in twenty that
  its node does not judge valid. (Two more answers of 500 and 520 came from other
  relays, once each.)
- **On the image of 17:12 UTC on the 25th, to 06:40 on the 26th** (it
  had a limit on the work one transaction may cost, under what is not done): 4,037 slots went by
  and a bid was sent in 3,964 of them, 98.2%. Of the 73 without: in 65 no relay held a registration
  from the proposer, seven were built and not sent, and one was asked for and not built. 24,938 bids
  were sent. 24,905 were judged valid afterwards; the other 33 were not judged, because the guest
  shows the feeder no block while it holds a sealed message, and for six slots it held made-up ones
  handed in through the public door to try it. Five rounds ended after their slot began. Seven rounds
  a slot and the last bid 0.78 s before the slot, at the median. Of 79,396 answers 55,287 were 200
  and 23,958 were 202; 20 posts had no answer, and three answers were 500 or 503.
- **Two relays refuse blocks that touch addresses on their lists, and that stopped it.** 126 answers
  of 400 in that time said "block accesses blacklisted address", for four addresses, from Flashbots'
  relay and Titan's; Ultrasound's and Aestus' took the same blocks. (Two more 400s were for other
  things.) They stayed under one answer in twenty until 06:38 on the 26th: in the two minutes from
  then 64 came, for blocks of six slots, and the feeder stopped itself by its own rule. The feeder
  was then changed so that a relay that refuses a block for this is sent no more on that head, and
  was started again with that rule at 15:03 UTC the same day. Such transactions are not left out:
  the blocks that hold them still go to the relays that take them. From then to 23:48 that day no
  relay refused a block for this.
- **On the image of 15:19 to 19:10 UTC on the 26th** (the first with the hole under its stack and
  with what a request gave kept): 1,155 slots went by and a bid was sent in 1,144, 99.0%; in the
  other 11 no relay held a registration from the proposer. 9,281 bids sent, every one judged valid
  afterwards; no round ended after its slot began. Eight rounds a slot and the last bid 0.75 s
  before the slot, at the median. Of 29,646 answers 22,252 were 200 and 7,320 were 202; three posts
  had no answer and one answer was 503.
- **One relay says it is posted to too often.** The other 70 answers in those hours were 429, "too
  many requests", all from Ultrasound's relay and all after 17:19, when a change to the feeder
  brought a round down from 0.95 s to 0.76 s: never before a slot's seventh round, and then to every
  other one, which is what a limit of about one block a second looks like. The feeder now posts to a
  relay that has said so no more often than every 1.3 s, and its last block of a slot whenever it
  can tell which that is; the other three get every round. That relay therefore holds a bid of ours
  that is up to a second or so older than the others' for most of a slot.
- **On the image of 19:15 to 23:48 UTC on the 26th** (it decodes and checks the headers it is given
  once and not on every request, and turns a bid into a point of the curve with this project's
  arithmetic and no longer the third-party library's; a request took the guest less than half the
  time): 1,368 slots went by and a bid was sent in 1,311, 95.8%. Of the 57 without: in 24 no relay
  held a registration from the proposer, and 33 were built and nothing sent (next item). 15,474
  bids sent, every one judged valid afterwards; no round ended after its slot began. Twelve rounds a
  slot, 0.52 s a round, and the last bid 0.85 s before the slot, at the median. Of 44,562 answers
  38,514 were 200 and 6,034 were 202; five were 429, five were 400 (four for blocks on a parent or
  slot the relay had moved on from, one "simulation failed: could not find parent block"), and four
  posts had no answer.
- **Built and nothing sent, in 33 of those 1,368 slots.** Each of them had one round and no more.
  In nearly all the request was 10 MB or more and took the feeder 6 to 9 s to gather: the pool that
  night held transactions, several at a time, that each read about 1,100 storage slots, beside the
  kind that touches hundreds of accounts. The block that came of such a round either had nothing
  in it (about a quarter of them) or was ended by the guest more than half a second after the time
  its request allowed, and the guest sends neither. The image before had no such slot because its
  hours had no such transactions: all 33 came after 20:40 UTC. (Some thirty more slots had a last
  round with nothing in it and an earlier bid that stood; that is under what is not done.)
  For this the feeder has a rule since 00:53 UTC on the
  27th: a transaction's width is the accounts it touches and a quarter of the storage slots it
  reads, 99 in 100 are narrower than 60 and always proposed, and the wider ones of a round are
  proposed while they fit what the round has time for, which in a head's first round is little.
  In 60 slots where this is developed, with the same transactions in the pool, it held some back
  in twelve: every slot had a block sent, and no first round took more than 2.2 s where six of 40
  had taken 4.4 to 5.4 s without it. At the relays since, to 03:14 UTC on the 27th (705 slots), the
  only slots built for with nothing sent were the three the feed began an hour's run in. It is a choice
  by what a transaction costs to prove and not by whose it is, as the feeder's leaving out
  transactions that are slow to run is (under what is not done).
- **A flaw in the engine, found on the 26th and in every image before the one that runs now.** When a
  transaction is left out of a block because the proofs do not reach a storage slot it reads, the
  engine could keep that slot as an empty one, and a later transaction of the same block reading it
  would be run on a value the state does not have: an invalid block, bid for. No such block is
  known, and each one counted above as valid was judged by a node after it was built; a relay that
  checks blocks would refuse one. It is put right in the source and tested there
  ([THREAT_MODEL.md](THREAT_MODEL.md) has the whole of it), and the image that runs since 23:53 UTC
  on the 26th has the correction.
- **Two hours on one image looked at closely** (the third of the eight there have been; from 04:28 UTC on
  the 25th, 600 slots): 3,172 blocks built and 3,102 sent. Of the 70 not sent, 42 were for proposers no
  relay had a registration from, 26 paid no more than one already sent for the slot, and two were too
  late. Of 9,934 answers 7,024 were 200, 2,907 were 202 and three were none; none was a refusal.
- **Timing** in those two hours: two of the 3,102 bids had their round end after the slot began, by 0.6
  s and 0.8 s, both in rounds in which one relay gave no answer in the time allowed. The last bid of a
  slot was in 0.81 s before it at the median. Five rounds a slot, 1.1 s a round at the median. A slot's last
  round is its largest: at the median of each part, 0.35 s of the feeder gathering transactions and
  proofs and 0.98 s of asking the guest, which is the request (2.2 MB by then) crossing the internet,
  the build, and the posts to the relays with their answers. Measured apart on an earlier image, those
  three took 0.15 s, 0.45 s and 0.07 s. Since 12:28 on the 25th the feeder no longer waits between
  rounds: in the two hours from 12:48 (600 slots) six rounds a slot at the median, and the last bid
  0.76 s before the slot.
- **The first hours were slower.** The first, from 18:30 UTC on the 24th: 1,121 blocks built and 1,088
  sent, four rounds a slot 1.6 s apart, two bids answered after their slot began. The hour from 19:58,
  on the next image: 1,540 built and 1,490 sent; 4,840 answers, of them 3,344 200, 1,495 202 and one
  none; no bid answered after its slot began.
- **Until the image of 04:27 on the 25th, Google's host reset the trust domain on about one request in
  eight for a quote** (17 of 130 on a test machine, three of fifteen on the running one). Three times in
  six hours (22:58 and 23:58 UTC on the 24th, 01:59 on the 25th) the guest asked to have a quote made,
  the call never returned, and the trust domain was started afresh with nothing on its console. Every
  start draws new keys, so for more than three hours that night its bids at the relays were under keys
  this repository did not name; the bidding went on, some slots later each time. The cause was found by
  trial: the firmware keeps a timer interrupt going every 10 ms, and the resets came when one fell due
  while the host was making the quote. Why the host does that is not known here. A Linux guest, which
  does not run the firmware's timer, got 350 quotes of
  350. That image stopped the timer for the call: 818 requests on Google's machines (768 on a test
  machine, 50 on the running one) and no reset. The images since stop it once, when they start:
  on the first two of them 505 requests (400 on a test machine, 105 on the running ones) and no
  reset. Once in those, the
  connection for the next request was not made in the ten seconds allowed, with the guest still up
  and under the same key; that is not explained. The feeder, which asked every hour, now asks once
  for each start.
- **How a slot's last round came to nothing, image by image.** A slot's last round is begun as late as
  will fit, after a wait. On the image of 17:12 on the 25th, in 143 of 3,096 slots from Google Cloud (17:13 UTC on 2026-11-25 to 03:31 on
  the 26th; 182 of 4,037 by 06:40) that round's request, two megabytes sent from the machine with the node, was so long in
  arriving (0.38 s at the median, where the round before took 0.12 s) that the time it allowed for
  transactions was gone: the block had none in it, the guest kept it back, and the slot's last bid was
  an earlier round's, 3.1 s before the slot at the median. By the sending machine's own account
  of its TCP, packets lost between it and the guest hold its sending window near 150 packets and now
  and then far lower, and such a request is 1,200 or more. Those requests were larger than they
  need be: each carried again nearly everything the one before it did. The images since 15:19 on
  the 26th are sent only what they have not been. In a trial on Google Cloud with no relay (300 slots each way, one
  hour after the other) the last round's request was 0.25 MB at the median where it had been 2.2, a round took
  0.89 s where 1.07, and the last round still came to nothing in 6 slots of 300 where 10. What was
  left had another cause: a round built its block from nothing, so one left less time than the
  round before used could not do as well. On the image of 19:15 on the 26th, 38 of 1,368 slots at
  the relays had a last round with nothing in it. The image that runs now goes on from the block
  before (under what it does), and in 1,000 slots where this is developed three had such a last
  round, one of them its only round, the cases said under the numbers.
- **A full pool, and one slow transaction: what happened.** For three minutes on
  2026-11-25 the feeder had 400 transactions to propose, which is the most it takes from its node's
  pool; rounds took 6 to 12 s where they take one, and on Google Cloud five slots in a row went by with
  nothing sent. One call to the point evaluation precompile cost the guest 3 s: that arithmetic, and
  BLS12-381's for the precompiled contracts, is still Jaune's on numbers of any size, and the guest looked at its
  clock between transactions and not inside one. The feeder now leaves such transactions out and gives a
  round no more than fits its time. The image of 12:47 that day puts a full pool's transactions in order
  less wastefully: of four requests kept from those minutes, three were built in 55% to 70% of the time
  the image before took, and the fourth, the one with the point evaluation, in 86%. The pool filled
  again an hour and a half later and three times after: with the feeder's change every such slot had a
  bid, on Google Cloud (29 slots with 300 or more pending) and here (40), though in a third of the
  fullest only one bid, ready five seconds before the slot. (The feeder judged a second round by what
  the first had cost. It no longer does; in 40 slots here since, three of them full, every slot's last
  block was ready within 1.5 s of the slot.) The images since 17:12 on the 25th have a limit of their own, so that this
  no longer rests on the feeder: a table says what each precompiled contract costs in time for its
  input, from measurements on the guest's runtime, and a transaction in a block being built gets a
  quarter of a second of it; a call there is none left for fails without being run and the transaction
  is left out. With the feeder's filter off, the guest's longest round in 8,296 was 1.38 s (below, under one machine). What
  that leaves: the table is an estimate, and for four BLS12-381 contracts a guess above the ones
  measured; work outside precompiled contracts is bounded by gas alone, which was not measured against
  time; a transaction left out costs its quarter second again every round, since the feeder is not told;
  and transactions that need those contracts for longer than that are still not built in at all.
- **No proposer took one of its blocks**, and none was expected to.

**On one machine** (Xeon Gold 6526Y; guest in TDX; in place of the relays the test relay beside it, and
reth's validator to judge each block). An image built to post to the test relay is another file than the
one that posts to the real ones, with another measurement; the code is the same but for the list of
relays and their certificates' roots.

- 1,000 slots in a row on the code of the image that ran on Google Cloud until 12:47 UTC on the 25th,
  but for one later change to how a quote is asked for: every slot with a block sent, 6,790 blocks sent,
  every one judged valid by reth's validator and taken by the test relay, none late. Seven rounds a
  slot, 0.75 s apart; 0.35 s of the guest's work for each.
- 1,000 slots on the code after it (the firmware's timer stopped for good): 998 with a block sent, 6,627
  blocks, all valid. The two slots without were in three minutes of a full pool.
- 1,000 slots on the code that ran on Google Cloud from 12:47 to 17:05 on the 25th (it orders a full
  pool faster), with the feeder's limit on what a round carries: 999 with a block sent, the one without
  being the first, which the run joined 1.3 s before it. 7,189 blocks built and 7,039 sent, all valid,
  none late; eight rounds a slot at the median, 0.33 s of the guest's work for each. The feeder had as
  many transactions as it will propose (400) in twelve of those slots, and every one had a block sent.
- On the code of the image that ran on Google Cloud from 17:12 on the 25th, with the feeder leaving no transaction out for being slow, so
  that the guest's own limit was what was tried: 987 slots, for which the feeder asked 1,000 times
  (thirteen twice: it took a slot for empty after four seconds then, and the block came later). 8,271
  blocks built and 8,133 sent, all valid, none late; nine rounds a slot. The guest's longest round was
  1.38 s of 8,296, where a round with a slow transaction in it had taken as much as nine. The pool was
  full far more often than in any run before: 300 or more pending in 116 of the 1,000 and all 400 in 67.
  Two slots had no block that could be used, both for the feeder's time and not the guest's: once a
  proof was missing after 4.8 s of gathering and 0.3 s were left to mend it, and once the node had the
  new head nine seconds into its slot. How many transactions the guest's limit left out is not counted;
  the guest does not say.
- The runs since: 1,000 slots on the image of 23:53 on the 26th, under the numbers with the image
  that runs, and 1,000 on the image of 19:15 before it, of which this report gives only that it had
  14 rounds a slot (TODO.md has it).
- What "1,000 slots" means in the runs before the one on the image of 17:12: slots this was asked to build for. The feeder
  asked once for each new block of the chain, for the slot after it. In the run on the code of 12:47,
  1,003 slots went by; the three not counted followed a slot whose proposer proposed nothing, and
  nothing was built for them.
- Before those, on the two images before them: 999 slots each (each run joined its first slot too
  late), 7,017 and 6,415 blocks, all valid, none late.
- Three runs of 1,000 slots on earlier images: two with a block for every slot, one with 998.

[bn]: https://buildernet.org/blog/2025/04/28/buildernet-v1.3
[bn16]: https://buildernet.org/blog/2025/12/02/buildernet-v1.6
[jaune]: https://github.com/skbaek/jaune
[image-runs]: https://github.com/posix4e/cluck/actions/workflows/image.yml
