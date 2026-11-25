# A block builder in a trust domain, with far less inside it

A report on [`evm/`](evm/README.md), for people who build Ethereum blocks in trusted execution
environments. Written 2026-11-24 and revised on the 25th. The runs the numbers come from are recorded in
[TODO.md](TODO.md), most with their commands; some figures were counted from the runs' own records for
this report and stand nowhere else. Those records are files on the machine that made them and are not
published. What is weak is said here in short. It is said at length in the part of
[THREAT_MODEL.md](THREAT_MODEL.md) headed "The EVM service", which is kept as a dated record and is
right where the two differ; the rest of that file is about the same OS on other machines.

## The claim

A builder in a TEE asks whoever sends it transactions to trust what is inside the TEE. Where a builder
has said what that is, it is a Linux image: a kernel, an init system, a C library, a TLS
library, an execution client, the builder, and whatever configures them at boot. BuilderNet's nodes, for
one, were described in [its release notes of April 2025][bn] as full Linux TDX images holding rbuilder,
Reth, a proxy for order flow and one for attestation. The kernel, and anything that runs with its
rights, can read the transactions.

This is a builder whose guest is one EFI program of 4.0 MB. Above the firmware there is nothing else:
no kernel, no C library, no OpenSSL, no shell, no file system, and one listening TCP port. The network
card's driver, Ethernet, IP, TCP, DNS, TLS 1.3, X.509, HTTP, the EVM, the Merkle-Patricia trie, BLS
signing, SSZ and the builder itself are Lean in that one program. The 0.8% of it that is C parses no
frame, no request and no certificate. (Compiled Lean also carries small functions of Lean's own C
header inside it, which count references and reach into objects. They are counted here as Lean, and by
instructions they are most of the compiled code: the figure is under what is trusted, below.)

It runs today in a TDX trust domain on Google Cloud, builds a block about every second from the public
pool, signs its bids with a key drawn inside the trust domain, and posts them itself to Flashbots,
Ultrasound, Aestus and Titan. Anyone can follow one of those bids from a relay's public list back to
the source it was built from; how is below.

Three things it is not. It is not a competitive builder: it sees only the public pool, and its blocks
were worth between a fifth and a third of the winning ones at the median, and less summed (the
measurements are below). It guards nothing private yet: the instance that is running holds a key for
signing bids, which guards no money, and no way is open for anybody outside to send it a sealed
transaction. And it is not the same shape as a builder with its node inside: here the node is outside
the trust domain and hands the guest transactions with proofs of the state they touch. That is what lets
the inside be small. It also means the machine that feeds it sees the public flow and chooses what the
builder sees of it. Private flow has to be sealed to the guest, which is shown here for single
transactions that this project sent to itself, and has limits said below. So the 4.0 MB is the size of a
builder that does not yet do a winning builder's work.

Words used below. The *guest* is the program in the trust domain. The *host* is the machine it runs on
and whoever runs that: on Google Cloud, Google. The *feeder* is another machine, ours, with an ordinary
node; it sends the guest transactions and proofs over the internet. A *round* is one request of the
feeder's and the block the guest builds and sends for it; a slot has several. A transaction is *sealed*
when it is encrypted to a key the guest drew, so that the feeder carries it without reading it. The
*test relay* is a small program of ours that takes whatever it is sent, as a relay would, and writes it
down.

## What is inside

The image as it runs on Google Cloud, counted from the linker's map and the file
(`scripts/image-inventory`):

| Part | Bytes | Share | Whose |
|---|---:|---:|---|
| The builder: engine, trie, TLS, bids, relays | 1,397,491 | 35.5% | this project's Lean |
| Lean's own library | 1,320,301 | 33.5% | Lean's |
| What is left of Jaune, an executable specification of the EVM in Lean | 761,501 | 19.3% | a third party's ([skbaek/jaune][jaune]), in a fork with changes made here |
| The OS: card drivers, Ethernet to TCP, DNS | 365,488 | 9.3% | this project's Lean |
| Start-up and constants of compiled modules, relocations, and 1,093 bytes of two libraries (batteries, mathlib) | 61,793 | 1.6% | the compiler's, the linker's, those libraries' |
| C | 29,622 | 0.8% | 2,875 lines printed at build time from programs kept as data in Lean (`Mini/`), 1,273 by hand |
| Counted | 3,936,196 | | shares are of this; the file is 4,014,080 bytes, the rest its headers, the linker's own tables and padding |

About 15,000 lines of Lean written here are in it (66 modules, 14,776 lines with their comments): the
OS's network and drivers, the builder, the execution engine, TLS and its cryptography. The C is the
allocator and reference counting that compiled Lean stands on, the entry from firmware, the primitives
the drivers call to reach a device's registers and memory, and the TDX calls for a report and a quote.
It moves bytes and addresses that come from firmware and from devices; it interprets none that come over
the network.

What that count leaves out or flatters:

- **Firmware is not in it**, and stays underneath the whole time. The firmware built from source where
  this was developed is a file of 4 MB, as large as the image, of compressed C; Google's cannot be
  looked into. See the next section.
- **No Linux image was measured for comparison**; one published size was looked up. The image of
  [BuilderNet v1.6][bn16] (December 2025, the last release with public notes) for TDX on Azure is a
  disk image of 326,107,648 bytes, which its notes say holds rbuilder, Reth, Lighthouse, FlowProxy,
  HAProxy, a proxy for attestation, an operator API and acme.sh on a Yocto Linux. That is 81 times
  the 4.0 MB here, and the two are not the same kind of thing: the file was not downloaded or looked
  into, a disk image has room in it that is not code, and theirs holds two clients that follow the
  chain inside the trust domain, where this builder is shown proofs against a header it is given
  (see what the feeder can still do, below). And a Linux guest all but leaves the firmware behind once
  its kernel has started, where this program never does (next section). "Far less" is a claim about
  kinds of thing, a kernel and what runs on it against one program, and that one number goes no further
  than that.
- **Jaune is someone else's code, a fifth of the image, and still does part of the work.** The
  interpreter that runs transactions was written here and is held to Jaune by tests; Jaune's own
  interpreter went out of the image on 2026-11-25 (the image was 4.9 MB with it, and a request could
  ask for a block built by it), and a request for it is now refused. Decoding blocks, headers and
  transactions, recovering senders, checking the header, the precompiled contracts with their curves and
  hashes, and the tries of transactions, withdrawals and receipts are still Jaune's. The fork used
  differs from upstream: in three places by code that nothing proves equal to the specification, and in
  one where the compiled code differs from the definition on purpose. Nobody here has reviewed Jaune
  itself.
- **The compilers are trusted**: Lean's, and the C compiler and linker behind it.
- **What is C is told by the file it was compiled from.** Compiled Lean is C that Lean's compiler wrote,
  built against Lean's own header, and the small functions of that header that end up inside it
  (counting references, reading a field) are counted as Lean. **They are most of it.** Of the 2,527,478
  bytes of code compiled here from Lean (this project's and Jaune's, 94 modules), 1,797,577, or 71%, are
  instructions whose source line is in that header; 292,913 (12%) have a line of the C the compiler
  wrote for the module, and 436,988 (17%) have no line. Half of the header's share is counting
  references. (`evm/scripts/header-share`, which compiles the same C again with line numbers in it: 8 of
  3,402 functions came out another size that way, 14 bytes between them. Lean's own library comes
  compiled and was not looked into.) So the rows above for this project's Lean and for Jaune say whose
  program the bytes carry out, not who wrote the instructions: seven in ten of those are from 3,590
  lines of C by Lean's authors, trusted here as the compiler is and reviewed by nobody here.
- **Two things under the Lean are not sound, and neither is mended.** The program runs on a stack of
  64 MiB with nothing below it to stop it: recursion past the end would write into the image, and how
  deep a hostile request can drive it has not been worked out. And seven of mathlib's start-up
  routines, which Jaune's modules draw in for the sake of proofs, are replaced by ones that do
  nothing: code that read a constant one of them would have built would read memory nothing has
  written. That the test suites pass is all that stands behind either. Nor does anything keep the
  image's code from being written or its data from being run: the pages are as the firmware mapped them.
- **Nothing proved covers the builder.** Parts of the runtime have proofs. The network stack and the
  builder are tested: the cryptography against OpenSSL's, the engine against Ethereum's own suites
  (4,723 files) and against Jaune, the blocks against reth's validator. That is evidence, not proof.
  Those suites are run by hand where this is developed: the repository's CI builds the image and tests
  the tools around it, not the builder's Lean, and Ethereum's suites were not run again for every image.
  The TLS and the cryptography under it were written here and have been read by nobody who writes such
  code for a living.

## What a relying party trusts

On Google Cloud:

1. **Intel**: the processor, the TDX module, the quoting enclave.
2. **Google's firmware.** It starts the guest and is never left: it owns the page tables and
   exceptions for as long as the program runs, shares its address space, and could read its keys. It
   is measured (MRTD), and Google signs a statement for that measurement, which is checked. What it
   does is Google's word; nobody else builds it. On a machine of one's own the firmware can be built
   from source, as it is where this was developed, and making it small would be the next reduction.
   What the program still asks of it once the card is up is three things: to print a line on the
   console, one for each request served; a counted delay of a millisecond when nothing has come from
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
   ready-made modules of mathlib it is linked against. That the image is the same file wherever it is
   built says the build can be repeated, and nothing about those.

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
  - What sealing still keeps from such a feeder: the bytes, the sender and the signature, until the
    block is in the chain; and the transaction cannot be changed, or built in after the last slot its
    sender named.

**Set beside a builder with its node inside**, for somebody deciding where to send a transaction:

- The same in kind. Both ask the sender to trust a measured image, the firmware under it and Intel.
  Both are reached over a network their host controls, and either can be starved by it.
- Less to trust here. What can read the transaction is one program whose parts are listed above, that
  anybody can build to the same file in minutes and check against the running guest's quote. It has
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
does that again about once a second until 0.7 s before the slot, each time with what has arrived since.

Three blocks built in the guest are on mainnet. One (26463293) was built from the public pool. Two
(26465583, 26470277) each hold a transaction that was sealed to the guest and that the feeder carried
without seeing. All three won because a test wallet paid the proposer, and that payment was signed by
the feeder, not in the guest. In both sealed cases the sender and the feeder were one program on one
machine, so they show that the parts fit and nothing about an adversary. They were built on one machine
here, where host and feeder are the same machine, by the images of 2026-11-21 and 22. No block built on
Google Cloud, or by the code now running, has been proposed.

## Numbers

**On Google Cloud** (`c3-standard-4` with TDX, us-central1), fed over the internet from a node 12 ms
away, bidding at four relays with nothing paid for a win:

- It has bid since 2026-11-24 18:30 UTC, and on the image described above since 2026-11-25 17:09. These
  are the first hours, not a long record, and the numbers below are of the images before that one. It
  differs from the last of them in one thing, a limit on the work one transaction may cost (under what
  is not done).
- **All of it, to 15:04 UTC on the 25th**: 6,167 slots went by and a bid of ours was sent to a relay in
  5,973 of them, 96.9%. Of the 194 without: in 94 no relay held a registration from the slot's proposer,
  so there was nobody to send to; 71 were three changes of image, 23 or 24 slots each; seven were the
  three resets by Google's host (below), two or three slots each; 14 followed a slot with no block, for
  which nothing was built then (below); seven were built and not sent, five of them in the full pool of
  07:39 (below); and one has no record and no reason found. 30,132 bids were sent, every one judged
  valid afterwards by reth's validator on the feeder, and eight had their round end after the slot
  began. In that time the guest started seven times, each time with new keys: the first start, three
  changes of image, and the three resets.
- **What the relays answered**, to all of it: 97,241 answers (a block goes only to the relays that hold
  the proposer's registration, so to fewer than four on average). 66,460 were 200 and 30,666 were 202. A
  202 says the bid was below the relay's floor and the block was not checked, so only the 200s say a
  relay ran the block. Flashbots' and Ultrasound's public lists give these bids with
  `optimistic_submission` false. 27 posts had no answer in the 1.5 s allowed.
- **What they refused**, 26 answers of 400: eight "unknown parent hash" and five on the randomness, all
  thirteen for blocks built on the old parent when a block came late, a fault of the feeder's that is
  said under what is not done; seven "builder not in proposer's trusted list", from Aestus, which is a
  proposer's choice; three "payload attributes not (yet) known" from Flashbots; one "submission for
  wrong slot"; and two, for two blocks of one slot, "block accesses blacklisted address" from Titan.
  This builder leaves no transaction out for whose it is. Before Google Cloud, on 2026-11-24, relays
  refused three blocks that paid nothing; the guest has since refused to send such a block.
- **And one relay said it could not serve.** Ultrasound's answered 503 to every post of three separate
  minutes on the 25th, 60 answers, while listing other builders' bids for the same slots; why is not
  known here. The feed, which stops itself when more than one answer in twenty is not a 200 or 202,
  stopped at 15:04, and was started again at 15:07 with a rule that leaves such a relay alone for ten
  minutes and longer and goes on with the others. (Two more answers of 500 and 520 came from other
  relays, once each.)
- **Two hours on one image looked at closely** (the third of the five there have been; from 04:28 UTC on
  the 25th, 600 slots): 3,172 blocks built and 3,102 sent. Of the 70 not sent, 42 were for proposers no
  relay had a registration from, 26 paid no more than one already sent for the slot, and two were too
  late. Of 9,934 answers 7,024 were 200, 2,907 were 202 and three were none; none was a refusal.
- **Timing** in those two hours: two of the 3,102 bids had their round end after the slot began, by 0.6
  s and 0.8 s, both in rounds in which one relay gave no answer in the time allowed. The last bid of a
  slot was in 0.81 s before it at the median. Five rounds a slot, 1.1 s apart: about 0.35 s of that is
  the feeder gathering transactions and proofs, and the other 0.75 s is the request (2.2 MB late in a
  slot) crossing the internet, the build, and the posts to the relays with their answers. Measured apart
  on an earlier image, those three took 0.15 s, 0.45 s and 0.07 s. Since 12:47 on the 25th the feeder no
  longer waits between rounds: seven rounds a slot, and the last bid 0.75 s before the slot at the
  median, in its first two hours.
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
  machine, 50 on the running one) and no reset. The two images since stop it once, when they start:
  505 requests (400 on a test machine, 105 on the running ones) and no reset. Once in those, the
  connection for the next request was not made in the ten seconds allowed, with the guest still up
  and under the same key; that is not explained. The feeder, which asked every hour, now asks once
  for each start.
- **No proposer took one of its blocks**, and none was expected to.
- The machine costs about 23 cents an hour.

**On one machine** (Xeon Gold 6526Y; guest in TDX; in place of the relays the test relay beside it, and
reth's validator to judge each block). An image built to post to the test relay is another file than the
one that posts to the real ones, with another measurement; the code is the same but for the list of
relays and their certificates' roots.

- 1,000 slots in a row on the code of the image that ran on Google Cloud until 12:47 UTC on the 25th,
  but for one later change to how a quote is asked for: every slot with a block sent, 6,790 blocks sent,
  every one judged valid by reth's validator and taken by the test relay, none late. Seven rounds a
  slot, 0.75 s apart; 0.35 s of the guest's work for each.
- 1,000 slots on the code after it (the firmware's timer stopped for good): 998 with a block sent, 6,627
  blocks, all valid. The two slots without were in the three minutes of a full pool, below.
- 1,000 slots on the code that ran on Google Cloud from 12:47 to 17:05 on the 25th (it orders a full
  pool faster), with the feeder's limit on what a round carries: 999 with a block sent, the one without
  being the first, which the run joined 1.3 s before it. 7,189 blocks built and 7,039 sent, all valid,
  none late; eight rounds a slot at the median, 0.33 s of the guest's work for each. The feeder had as
  many transactions as it will propose (400) in twelve of those slots, and every one had a block sent.
- On the code now running on Google Cloud, with the feeder leaving no transaction out for being slow, so
  that the guest's own limit was what was tried: 987 slots, for which the feeder asked 1,000 times
  (thirteen twice: it took a slot for empty after four seconds then, and the block came later). 8,271
  blocks built and 8,133 sent, all valid, none late; nine rounds a slot. The guest's longest round was
  1.38 s of 8,296, where a round with a slow transaction in it had taken as much as nine. The pool was
  full far more often than in any run before: 300 or more pending in 116 of the 1,000 and all 400 in 67.
  Two slots had no block that could be used, both for the feeder's time and not the guest's: once a
  proof was missing after 4.8 s of gathering and 0.3 s were left to mend it, and once the node had the
  new head nine seconds into its slot. How many transactions the guest's limit left out is not counted;
  the guest does not say.
- What "1,000 slots" means in the runs before that one: slots this was asked to build for. The feeder
  asked once for each new block of the chain, for the slot after it. In the run on the code of 12:47,
  1,003 slots went by; the three not counted followed a slot whose proposer proposed nothing, and
  nothing was built for them.
- Before those, on the two images before them: 999 slots each (each run joined its first slot too
  late), 7,017 and 6,415 blocks, all valid, none late.
- Three runs of 1,000 slots on earlier images: two with a block for every slot, one with 998.

**Against the blocks proposers took**, as relays' public lists give what each paid. Measured eight
times, over up to 875 slots each: ours was 18% to 34% of theirs at the median, and 4.5% to 31%
summed. The three largest and latest:

- From Google Cloud at the real relays (the hour from 04:28 UTC on 2026-11-25, 267 slots for which a
  relay listed what the proposer was paid): ours 34% of theirs at the median and 31% summed; 80% at
  best, never more.
- On one machine against the test relay (2026-11-22 and 23, three runs of 1,000 slots): 29%, 27% and 29%
  at the median; 19% and 17% summed in the first two, and the third was not summed.
- On one machine at the real relays (2026-11-24, 253 slots): 18% at the median and 4.5% summed, in an
  hour when the taken blocks were worth twice what they had been the night before.

The summed figure is the truer one: the slots that pay are far above the median, and in those ours is
furthest behind. Of what the taken blocks held that was public a second before the slot, ours held 84%
to 91% by fees summed over a run, and 89% to 94% at the median (four runs). So most of what it lacks was
never public, and some of it was public and not taken.

**How fast the parts are.** Building a block takes the guest 0.33 s at the median on the machine it was
developed on and 0.45 s on Google's; reth imports a block in 0.04 s. A request of 1.5 MB crosses the
internet into the guest's TCP in 0.15 s; late in a slot requests are 2.2 MB. A post to four relays takes
0.07 s on connections the guest keeps open.

## Check it yourself

A relay lists every bid it is sent with the key that signed it. The guest says, in a TDX quote, that
the key is its own. So a bid can be followed back to source with nothing from us but this repository:

1. **The bid.** Ask a relay for the bids under the builder's key;
   [`docs/live/builder.txt`](docs/live/builder.txt) has the key and a link. Flashbots, Ultrasound and
   Aestus list them; Titan gave no answer when asked.
2. **The key is the guest's.** `docs/live/builder.quote` is the guest's answer to "what is your key",
   quoted by the machine it runs on. <https://posix4e.github.io/cluck/live.html> checks it in a browser,
   as far as a page can: it takes the image's measurement from a file of ours.
3. **The guest is this program, on Google's firmware.** Check out the commit `docs/live/builder.txt`
   names (the repository has usually moved on from it), build the image, and run the command given
   there. `scripts/gce-check` asks five things: that the quote's signatures lead to
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
- The guest's port is plain TCP that asks nobody who they are, and a firewall rule of Google's lets in
  the feeder's address alone. Whoever can send from that address, or stands between, can do what the
  feeder can. A program stands beside the port for everybody else and passes on only requests for a
  key with its quote, and sealed transactions (`evm/builder/door`, at the address in
  `docs/live/door.json` since 2026-11-25): through it anybody can have a quote made for random bytes
  of their own, which <https://posix4e.github.io/cluck/send.html> does before it seals anything. It
  runs on an ordinary machine of Google's that is measured by nobody and could ask the guest whatever
  the feeder can; no transaction of a stranger's has come through it yet, and none has landed.
- A guest that starts again has new keys, and the record here is written by hand after a start.
  The feeder says when the two differ; until someone acts on that, the page of step 2 names a key
  the guest no longer has, as it did for more than three hours in the night of 2026-11-24.

## What is not done

- **It does not win.** No private order flow, no bundles, no blobs, nothing paid to the proposer beyond
  what the block earns. None of that is shown, and bundles and a payment signed inside would be new code
  inside; how much has not been measured.
- **It is not fast.** One core, one block at a time, about a second a round, and it stops 0.7 s short
  of the slot. Builders that win bid until the slot begins.
- **A full pool, or one transaction, has kept it from bidding, and may again.** For three minutes on
  2026-11-25 the feeder had 400 transactions to propose, which is the most it takes from its node's
  pool; rounds took 6 to 12 s where they take one, and on Google Cloud five slots in a row went by with
  nothing sent. One call to the point evaluation precompile cost the guest 3 s: that arithmetic, and
  BLS12-381's, is still the third-party library's on numbers of any size, and the guest looked at its
  clock between transactions and not inside one. The feeder now leaves such transactions out and gives a
  round no more than fits its time. The image of 12:47 that day puts a full pool's transactions in order
  less wastefully: of four requests kept from those minutes, three were built in 55% to 70% of the time
  the image before took, and the fourth, the one with the point evaluation, in 86%. The pool filled
  again an hour and a half later and three times after: with the feeder's change every such slot had a
  bid, on Google Cloud (29 slots with 300 or more pending) and here (40), though in a third of the
  fullest only one bid, ready five seconds before the slot. (The feeder judged a second round by what
  the first had cost. It no longer does; in 40 slots here since, three of them full, every slot's last
  block was ready within 1.5 s of the slot.) The image now running has a limit of its own, so that this
  no longer rests on the feeder: a table says what each precompiled contract costs in time for its
  input, from measurements on the guest's runtime, and a transaction in a block being built gets a
  quarter of a second of it; a call there is none left for fails without being run and the transaction
  is left out. With the feeder's filter off, the guest's longest round in 8,296 was 1.38 s (above). What
  that leaves: the table is an estimate, and for four BLS12-381 contracts a guess above the ones
  measured; work outside precompiled contracts is bounded by gas alone, which was not measured against
  time; a transaction left out costs its quarter second again every round, since the feeder is not told;
  and transactions that need those contracts for longer than that are still not built in at all.
- **After a slot with no block it has bid once.** The feeder asked for a block only when the chain had a
  new one, so when a proposer proposed nothing this builder sat the next slot out: three slots in a
  thousand in the last run here, and the same in every number above. Since 12:28 UTC on 2026-11-25 the
  feeder builds for the next slot on the same parent once a slot has gone some seconds with no block.
  That was tried by pretending slots were empty (115 blocks, all valid by reth's validator), and that
  afternoon a slot stayed empty while the builder on Google Cloud was bidding (15732467): it built three
  blocks for the slot after, and all four relays answered 200 to the first two. One slot is not a rate.
  And a block that comes late looks the same as none until it comes. The wait was four seconds at first,
  and blocks are the head at the feeder's node later than that once in 29, an epoch's first block nearly
  always: nine bids on the old parent drew the thirteen refusals above in three hours. The wait is
  now seven seconds, and the feeder looks once more for a late block before it asks the guest. About one
  head in 370 is later than that, and for those a bid on the old parent can still go out, which a relay
  that has the late block refuses.
- **One feeder, at somebody's home.** When that machine or its link stops, the builder stops.
- **Side channels.** The key's field arithmetic was written to take the same steps whatever the key,
  and a script reads its machine code for conditional jumps (`evm/scripts/check-secret-code`). The
  curve arithmetic above it is not read that way, nothing was measured on a running guest, and no
  other code here had that care. Firmware shares the guest's address space.
- **More than one port answers.** One TCP port listens. The guest also answers ARP, pings and IPv6
  neighbour discovery, puts fragments together, and reads DNS answers and everything the relays send.
  All of that is Lean; none of it is proved.
- **Certificates** are not checked for revocation, and the date they are judged at is the feeder's
  word.
- **Young code, all of it, and read by nobody else.** The repository's first commit is of 2026-11-16 and
  the builder's of 2026-11-19; the engine that runs the transactions is of the 21st, and the TCP was
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

The image:

    git clone https://github.com/posix4e/cluck && cd cluck/evm
    # for the very file that is running, first: git checkout the commit docs/live/builder.txt names
    # fetch mathlib's ready-made modules first: the command is in evm/README.md
    lake build
    scripts/build-efi tdx                 # .lake/build/efi/tdx/evm-os/BOOTX64.EFI

On a machine with TDX and a TDVF built from source (`TDX.md`; `SILO_TDVF` names the firmware file):

    scripts/run-fixtures tdx --key        # starts it, asks, checks the answers

On Google Cloud, `../scripts/gce-try` starts the same file on a TDX machine. The guest takes the
address 10.0.2.15 with its gateway at 10.0.2.1, so it needs a subnet of 10.0.2.0/24, a public address,
and a firewall rule that lets the feeder reach TCP 5005; the script's heading says how each is given.
A project's `default` network there also lets anyone reach every machine by ICMP and on TCP 22 and
3389, which a second rule has to close (`THREAT_MODEL.md` says what was open here, and until when).
Given the feeder's address as `SILO_GCE_FROM`, the script makes both rules (`../scripts/gce-wall`) and
lists every rule that can still let something reach the machine.

To feed it you need a synced reth with the `txpool`, `flashbots` and `debug` APIs and the patch in
`evm/builder/reth-state-witness.patch`, and a beacon node:

    builder/feed ADDRESS DIR --hold       # builds every slot and posts nothing; without --hold it bids

[bn]: https://buildernet.org/blog/2025/04/28/buildernet-v1.3
[bn16]: https://buildernet.org/blog/2025/12/02/buildernet-v1.6
[jaune]: https://github.com/skbaek/jaune
[image-runs]: https://github.com/posix4e/cluck/actions/workflows/image.yml
