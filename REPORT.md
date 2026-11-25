# A block builder in a trust domain, with far less inside it

A report on [`evm/`](evm/README.md), for people who build Ethereum blocks in trusted execution
environments. Written 2026-11-24 and revised on the 25th. The numbers are from runs that
[TODO.md](TODO.md) records with their commands; the records of the runs themselves are files on the
machine that made them and are not published. What is weak is said here in short. It is said at length
in the part of [THREAT_MODEL.md](THREAT_MODEL.md) headed "The EVM service", which is kept as a dated
record and is right where the two differ; the rest of that file is about the same OS on other machines.

## The claim

A builder in a TEE asks whoever sends it transactions to trust what is inside the TEE. For the builders
that run in trust domains today that is a Linux image: a kernel, an init system, a C library, a TLS
library, an execution client, the builder, and whatever configures them at boot. BuilderNet's nodes, for
one, were described in [its release notes of April 2025][bn] as full Linux TDX images holding rbuilder,
Reth, a proxy for order flow and one for attestation. The kernel, and anything that runs with its
rights, can read the transactions.

This is a builder whose guest is one EFI program of 4.0 MB. Above the firmware there is nothing else:
no kernel, no C library, no OpenSSL, no shell, no file system, and one listening TCP port. The network
card's driver, Ethernet, IP, TCP, DNS, TLS 1.3, X.509, HTTP, the EVM, the Merkle-Patricia trie, BLS
signing, SSZ and the builder itself are Lean in that one program. The 0.8% of it that is C parses no
frame, no request and no certificate.

It runs today in a TDX trust domain on Google Cloud, builds a block about every second from the public
pool, signs its bids with a key drawn inside the trust domain, and posts them itself to Flashbots,
Ultrasound, Aestus and Titan. Anyone can follow one of those bids from a relay's public list back to
the source it was built from; how is below.

Three things it is not. It is not a competitive builder: it sees only the public pool, and its blocks
were worth between a fifth and a third of the winning ones at the median (18%, 29% and 34% in three
measurements) and less summed. It guards nothing private yet: the instance that is running holds a key
for signing bids, which guards no money, and no way is open for anybody outside to send it a sealed
transaction. And it is not the same shape as a builder with its node inside: here the node is outside the trust domain and hands the guest transactions with proofs of
the state they touch. That is what lets the inside be small. It also means the machine that feeds it
sees the public flow and chooses what the builder sees of it. Private flow has to be sealed to the
guest, which is shown here for single transactions that this project sent to itself, and has limits
said below.

## What is inside

The image as it runs on Google Cloud, counted from the linker's map and the file
(`scripts/image-inventory`):

| Part | Bytes | Share | Whose |
|---|---:|---:|---|
| The builder: engine, trie, TLS, bids, relays | 1,388,281 | 35.4% | this project's Lean |
| Lean's own library | 1,320,290 | 33.6% | Lean's |
| What is left of Jaune, an executable specification of the EVM in Lean | 761,501 | 19.4% | a third party's ([skbaek/jaune][jaune]), in a fork with changes made here |
| The OS: card drivers, Ethernet to TCP, DNS | 365,488 | 9.3% | this project's Lean |
| Start-up and constants of compiled modules, relocations, and 1,093 bytes of two small libraries | 61,741 | 1.6% | the compiler's, the linker's, mathlib's |
| C | 29,622 | 0.8% | 2,875 lines printed at build time from programs kept as data in Lean (`Mini/`), 1,273 by hand |
| Counted | 3,926,923 | | the file is 4,004,864 bytes |

About 15,000 lines of Lean written here are in it (66 modules, 14,660 lines with their comments): the
OS's network and drivers, the builder, the execution engine, TLS and its cryptography. The C is the allocator and reference counting that compiled
Lean stands on, the entry from firmware, the primitives the drivers call to reach a device's registers
and memory, and the TDX calls for a report and a quote. It moves bytes and addresses that come from
firmware and from devices; it interprets none that come over the network.

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
  (see what the feeder can still do, below). "Far less" is a claim about kinds of thing, a kernel
  and what runs on it against one program, and that one number goes no further than that.
- **Jaune is someone else's code, a fifth of the image, and still does part of the work.** The
  interpreter that runs transactions was written here and is held to Jaune by tests; Jaune's own
  interpreter went out of the image on 2026-11-25 (the image was 4.9 MB with it, and a request could
  ask for a block built by it), and a request for it is now refused. Decoding blocks, headers and
  transactions, recovering senders, checking the header, the precompiled contracts with their curves
  and hashes, and the tries of transactions, withdrawals and receipts are still Jaune's. The fork
  used differs from upstream, in three places by code that nothing proves equal to the specification.
- **The compilers are trusted**: Lean's, and the C compiler and linker behind it.
- **Two things under the Lean are not sound, and neither is mended.** The program runs on a stack of
  64 MiB with nothing below it to stop it: recursion past the end would write into the image, and how
  deep a hostile request can drive it has not been worked out. And seven of mathlib's start-up
  routines, which Jaune's modules draw in for the sake of proofs, are replaced by ones that do
  nothing: code that read a constant one of them would have built would read memory nothing has
  written. That the test suites pass is all that stands behind either.
- **Nothing proved covers the builder.** Parts of the runtime have proofs. The network stack and the
  builder are tested: the cryptography against OpenSSL's, the engine against Ethereum's own suites
  (4,723 files) and against Jaune, the blocks against reth's validator. That is evidence, not proof.

## What a relying party trusts

On Google Cloud:

1. **Intel**: the processor, the TDX module, the quoting enclave.
2. **Google's firmware.** It starts the guest and is never left: it owns the page tables and
   exceptions for as long as the program runs, shares its address space, and could read its keys. It
   is measured (MRTD), and Google signs a statement for that measurement, which is checked. What it
   does is Google's word; nobody else builds it. On a machine of one's own the firmware can be built
   from source, as it is where this was developed, and making it small would be the next reduction.
3. **The image**, measured into RTMR1 together with the partition table of the disk it starts from.
   Anyone can work that value out from the image's file.
4. **Four certificate roots** the image holds for the relays' names, and every authority under them.
5. **What built the image**: Lean's compiler, the C compiler and linker that come with it, and the
   ready-made modules of mathlib it is linked against. That the image is the same file wherever it is
   built says the build can be repeated, and nothing about those.

Not trusted, and what it can still do: the host, the cloud's network, and the machine that feeds the
builder. The feeder runs an ordinary node and hands the guest pending transactions, the parent block's
header and proofs of the state they touch; the guest checks every proof against the state root in that
header. The header itself is the feeder's word: the guest does not know what the chain's head is.

- The feeder can starve the builder, choose what it sees of the public pool, and add transactions of
  its own.
- It names the slot, the proposer, the fee recipient, the time, the randomness and the withdrawals,
  and the guest signs a bid for whatever it then builds, as often as it is asked. A block built on
  inputs that are not the chain's is for a relay to refuse.
- It cannot have the guest sign anything but a bid for a block the guest has just built, and it cannot
  get the key.
- It does not see a transaction sealed to the guest, and can still learn much about one.
  - Unless the sender brings the proofs, the host is asked for them and so learns which accounts and
    storage the transaction touches.
  - The relays publish each bid's gas, value and count of transactions, so the host can tell whether
    a sealed transaction went in and what it paid.
  - A host that works at it can find out what the transaction does without reading it. It chooses
    the other transactions of the block and may write them. One of its own put before the sealed one
    sets the state the sealed one runs in; one put after reads what the sealed one changed; the
    relay's figures say how each fared. A few such blocks over a few slots can show which contract
    it touched and which way and how far it moved a price, which is most of what a trade is hidden
    for. No rule about order mends this (THREAT_MODEL.md has the ones thought through). None of this
    asking has been tried here.
  - What sealing still keeps from such a host: the bytes, the sender and the signature, until the
    block is in the chain; and the transaction cannot be changed, or built in after the last slot its
    sender named.

## What it does

Each slot the guest is handed pending transactions and proofs, builds a block, signs the bid with a BLS
key drawn inside the guest, and posts block and bid to the relays over TLS connections of its own. It
does that again about once a second until 0.7 s before the slot, each time with what has arrived since.

Three blocks built in the guest are on mainnet. One (26463293) was built from the public pool. Two
(26465583, 26470277) each hold a transaction that was sealed to the guest and that the host carried
without seeing. All three won because a test wallet paid the proposer, and that payment was signed on
the host, not in the guest. In both sealed cases the sender and the host were one program on one
machine, so they show that the parts fit and nothing about an adversary. They were built on one machine
here, before Google Cloud.

## Numbers

**On Google Cloud** (`c3-standard-4` with TDX, us-central1), fed over the internet from a node 12 ms
away, bidding at four relays with nothing paid for a win:

- It has bid since 2026-11-24 18:30 UTC, and on the image described above since 2026-11-25 12:47.
  These are the first hours, not a long record, and the numbers that follow are of the images before
  this one: it differs from the last of them in how a full pool is put in order and in when the
  firmware's timer is stopped, and its own first day is not over.
- **Two hours on the image before this one**, from 04:28 UTC on the 25th, 600 slots: 3,172 blocks built
  and 3,102 sent. Of the 70 not sent, 42 were for proposers no relay had a registration from, 26 paid no
  more than one already sent for the slot, and two were too late. Every block sent was judged valid by
  reth's validator on the feeding machine.
- **What the relays said**: of 9,934 answers, 7,024 were 200, 2,907 were 202 and three posts went
  unanswered in the 1.5 s allowed. None was a refusal. A 202 says the bid was below the relay's floor
  and the block was not checked, so only the 200s say a relay ran the block. Flashbots' and
  Ultrasound's public lists give these bids with `optimistic_submission` false.
- **Timing**: two of the 3,102 bids had their round end after the slot began, by 0.6 s and 0.8 s,
  both in rounds in which one relay gave no answer in the time allowed. The last bid of a slot was in
  0.81 s before it at the median. Five builds a slot, 1.1 s apart: about 0.35 s of each is the feeder
  gathering transactions and proofs, and the rest is the request (2.2 MB late in a slot) crossing the
  internet, the build, and the posts to four relays with their answers. Measured apart on an earlier
  image, those three took 0.15 s, 0.45 s and 0.07 s.
- **On the images before that**, ten hours from 18:30 UTC on the 24th, the same picture. The hour from
  19:58, for one: 1,540 blocks built and 1,490 sent, all valid; 4,840 answers, of them 3,344 200,
  1,495 202 and one unanswered; no bid answered after its slot began.
- **Until the image of 04:27 on the 25th, Google's host reset the trust domain on about one request
  in ten for a quote.** Three times in six hours (22:58 and 23:58 UTC on the 24th, 01:59 on the 25th) the guest
  asked to have a quote made, the call never returned, and the trust domain was started afresh with
  nothing on its console. Every start draws new keys, so for more than three hours that night its
  bids at the relays were under keys this repository did not name; the bidding went on, some slots
  later each time. The cause was found by trial: the firmware keeps a timer interrupt going every
  10 ms, and the resets came when one fell due while the host was making the quote. Why the host does
  that is not known here. A Linux guest, which does not run the firmware's timer, got 350 quotes of
  350. That image stopped the timer for the call: 818 requests on Google's machines (768 on a test
  machine, 50 on the running one) and no reset. The one now running stops it once, when it starts:
  450 requests (400 on a test machine, 50 on the running one) and no reset. The feeder, which asked
  every hour, now asks once for each start.
- **No proposer took one**, and none was expected to.
- The machine costs about 23 cents an hour.

**On one machine** (Xeon Gold 6526Y; guest in TDX; in place of the relays a test relay beside it,
which takes and writes down whatever it is sent, and reth's validator to judge each block):

- 1,000 slots in a row on the code of the image that ran until 12:47 UTC on the 25th, but for one later
  change to how a quote is asked for, and built to post to the test relay and not the real ones: every
  slot with a block sent, 6,790 blocks sent, every one judged valid by reth's validator and accepted by
  the stand-in, none late. Seven builds a slot, 0.75 s apart; 0.35 s of the guest's work for each.
- 1,000 slots on the image after it (the firmware's timer stopped for good): 998 with a block sent,
  6,627 blocks, all valid. The two slots without were in the three minutes of a full pool, below.
- 1,000 slots on the image now running (the one that orders a full pool faster), built for the test
  relay, with the feeder's limit on what a round carries: 999 with a block sent, the one without being the
  first, which the run joined 1.3 s before it. 7,039 blocks, all valid, none late; eight builds a
  slot, 0.33 s of the guest's work for each. The pool was full (400 pending) in twelve of those
  slots and every one had a block sent.
- What "1,000 slots" means in all of these: slots this was asked to build for. The feeder asks once
  for each new block of the chain, for the slot after it. In the last run 1,003 slots went by; the
  three not counted followed a slot whose proposer proposed nothing, and nothing was built for them.
- The same on the two images before it: 999 slots each (each run joined its first slot too late),
  7,017 and 6,415 blocks, all valid, none late.
- Three runs of 1,000 slots on earlier images: two with a block for every slot, one with 998.

**Against the blocks proposers took**, as relays' public lists give what each paid. Measured three
times:

- From Google Cloud at the real relays (the hour from 04:28 UTC on 2026-11-25, 267 slots with a
  figure): ours 34% of theirs at the median and 31% summed; 80% at best, never more.
- On one machine against the test relay (2026-11-23, 875 slots): 29% at the median. In the run before
  it (864 slots) 29% at the median and 19% summed.
- On one machine at the real relays (2026-11-24, 253 slots): 18% at the median and 4.5% summed, in an
  hour when the taken blocks were worth twice what they had been the night before.

The summed figure is the truer one: the slots that pay are far above the median, and in those ours is
furthest behind. Of what the taken blocks held that was public a second before the slot, ours held 94%
by fees (the 875 slots); what it lacks is what was never public.

**How fast the parts are.** Building a block takes the guest 0.3 s on the machine it was developed on
and 0.45 s on Google's; reth imports a block in 0.04 s. A request of 1.5 MB crosses the internet into
the guest's TCP in 0.15 s. A post to four relays takes 0.07 s on connections the guest keeps open.

## Check it yourself

A relay lists every bid it is sent with the key that signed it. The guest says, in a TDX quote, that
the key is its own. So a bid can be followed back to source with nothing from us but this repository:

1. **The bid.** Ask a relay for the bids under the builder's key; [`docs/live/builder.txt`](docs/live/builder.txt)
   has the key and a link. Flashbots, Ultrasound and Aestus list them; Titan gave no answer when asked.
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
   again whenever the record changes.

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
  the feeding machine's address alone. So you cannot ask it for a fresh quote yourself; the one in
  the repository is from when it started. A program to stand in front of the port and pass on only
  requests for a key with its quote, and sealed transactions (`evm/builder/door`), is written and
  runs nowhere yet.
- A guest that starts again has new keys, and the record here is written by hand after a start.
  The feeder says when the two differ; until someone acts on that, the page names a key the guest
  no longer has, as it did for more than three hours in the night of 2026-11-24.

## What is not done

- **It does not win.** No private order flow, no bundles, no blobs, nothing paid to the proposer beyond
  what the block earns. None of that is shown, and bundles and a payment signed inside would be new
  code inside.
- **It is not fast.** One core, one block at a time, about a second a round, and it stops 0.7 s short
  of the slot. Builders that win bid until the slot begins.
- **A full pool, or one transaction, can keep it from bidding.** For three minutes on 2026-11-25 the
  node had 400 transactions pending; rounds took 6 to 12 s where they take one, and on Google Cloud
  five slots in a row went by with nothing sent. One call to the point evaluation precompile cost the
  guest 3 s: that arithmetic, and BLS12-381's, is still the third-party library's on numbers of any
  size, and the guest looks at its clock between transactions and not inside one. The feeder now
  leaves such transactions out and gives a round no more than fits its time. The image now running
  builds a full pool's block in 55% to 70% of the time the one before took, by putting the
  transactions in order less wastefully. The pool filled again an hour and a half later and three times after:
  with the feeder's change every such slot had a bid, on Google Cloud (29 slots with 300 or more
  pending) and here (40), though in a third of the fullest only one, ready five seconds early. (The
  feeder judged a second round by what the first had cost. It no longer does; in 40 slots here since,
  three of them full, every slot's last block was ready within 1.5 s of the slot.) Transactions that
  call those precompiles are simply not built in, and one made to reach them only inside a block
  would still cost a slot.
- **After a slot with no block it has not been seen to bid.** The feeder asked for a block only when
  the chain had a new one, so when a proposer proposed nothing this builder sat the next slot out:
  three slots in a thousand in the last run here, and the same in every number above. The feeder now
  builds for the next slot on the same parent once a slot is four seconds old with no block. That was
  tried by pretending slots were empty (115 blocks, all valid by reth's validator); no relay has yet
  taken one built after a slot that really was.
- **One feeder, at somebody's home.** When that machine or its link stops, the builder stops.
- **Side channels.** The key's field arithmetic was written to take the same steps whatever the key,
  and a script reads its machine code for conditional jumps (`evm/scripts/check-secret-code`). The
  curve arithmetic above it is not read that way, nothing was measured on a running guest, and no
  other code here had that care. Firmware shares the guest's address space.
- **More than one port answers.** One TCP port listens. The guest also answers ARP, pings and IPv6
  neighbour discovery, puts fragments together, and reads DNS answers and everything the relays send.
  All of that is Lean; none of it is proved.
- **Certificates** are not checked for revocation, and the date they are judged at is the host's word.
- **Young code.** The TCP was rewritten and the driver for Google's card written in the week of these
  numbers.

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

To feed it you need a synced reth with the `txpool`, `flashbots` and `debug` APIs and the patch in
`evm/builder/reth-state-witness.patch`, and a beacon node:

    builder/feed ADDRESS DIR --hold       # builds every slot and posts nothing; without --hold it bids

[bn]: https://buildernet.org/blog/2025/04/28/buildernet-v1.3
[bn16]: https://buildernet.org/blog/2025/12/02/buildernet-v1.6
[jaune]: https://github.com/skbaek/jaune
[image-runs]: https://github.com/posix4e/cluck/actions/workflows/image.yml
