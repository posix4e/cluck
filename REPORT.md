# A block builder in a trust domain, with far less inside it

A report on [`evm/`](evm/README.md), for people who build Ethereum blocks in trusted execution
environments. Written 2026-11-24. Every number is from a run whose command and record are in
[TODO.md](TODO.md). What is weak is said here in short and in [THREAT_MODEL.md](THREAT_MODEL.md) at
length; where the two differ, that one is right.

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

Two things it is not. It is not a competitive builder: it sees only the public pool, and its blocks
were worth 29% of the winning ones at the median. And it is not the same shape as a builder with its
node inside: here the node is outside the trust domain and hands the guest transactions with proofs of
the state they touch. That is what lets the inside be small. It also means the machine that feeds it
sees the public flow and chooses what the builder sees of it. Private flow has to be sealed to the
guest, which is shown here for single transactions and has limits said below.

## What is inside

The image as it runs on Google Cloud, counted from the linker's map and the file
(`scripts/image-inventory`):

| Part | Bytes | Share | Whose |
|---|---:|---:|---|
| The builder: engine, trie, TLS, bids, relays | 1,383,958 | 35.3% | this project's Lean |
| Lean's own library | 1,320,269 | 33.7% | Lean's |
| What is left of Jaune, an executable specification of the EVM in Lean | 761,501 | 19.4% | a third party's ([skbaek/jaune][jaune]), in a fork with changes made here |
| The OS: card drivers, Ethernet to TCP, DNS | 365,488 | 9.3% | this project's Lean |
| Start-up and constants of compiled modules, relocations, and 1,093 bytes of two small libraries | 61,692 | 1.6% | the compiler's, the linker's, mathlib's |
| C | 29,683 | 0.8% | 2,875 lines printed at build time from programs kept as data in Lean (`Mini/`), 1,266 by hand |
| Counted | 3,922,591 | | the file is 4,000,256 bytes |

About 15,000 lines of Lean written here are in it: the OS's network and drivers, the builder, the
execution engine, TLS and its cryptography. The C is the allocator and reference counting that compiled
Lean stands on, the entry from firmware, the primitives the drivers call to reach a device's registers
and memory, and the TDX calls for a report and a quote. It moves bytes and addresses that come from
firmware and from devices; it interprets none that come over the network.

What that count leaves out or flatters:

- **Firmware is not in it**, is far larger than the image, and stays underneath the whole time. See
  the next section.
- **Jaune is someone else's code, a fifth of the image, and still does part of the work.** The
  interpreter that runs transactions was written here and is held to Jaune by tests; Jaune's own
  interpreter went out of the image on 2026-11-25 (the image was 4.9 MB with it, and a request could
  ask for a block built by it), and a request for it is now refused. Decoding blocks, headers and
  transactions, recovering senders, checking the header, the precompiled contracts with their curves
  and hashes, and the tries of transactions, withdrawals and receipts are still Jaune's. The fork
  used differs from upstream, in three places by code that nothing proves equal to the specification.
- **The compilers are trusted**: Lean's, and the C compiler and linker behind it.
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
3. **The image**, measured into RTMR1, which anyone can work out from the image's file.
4. **Four certificate roots** the image holds for the relays' names, and every authority under them.

Not trusted, and what it can still do: the host, the cloud's network, and the machine that feeds the
builder. The feeder runs an ordinary node and hands the guest pending transactions, the parent block's
header and proofs of the state they touch; the guest checks every proof against the state root in that
header.

- The feeder can starve the builder, choose what it sees of the public pool, and add transactions of
  its own.
- It names the slot, the proposer, the fee recipient, the time, the randomness and the withdrawals,
  and the guest signs a bid for whatever it then builds, as often as it is asked. A block built on
  inputs that are not the chain's is for a relay to refuse.
- It cannot have the guest sign anything but a bid for a block the guest has just built, and it cannot
  get the key.
- It does not see a transaction sealed to the guest. It can still learn about one: the relays publish
  each bid's gas and value, so a host that sets out to can find out whether a sealed transaction went
  in and what it paid; and unless the sender brings the proofs, the host is asked for them and so
  learns which accounts and storage the transaction touches.

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

- It has bid since 2026-11-24 18:30 UTC, and on the image described above since 2026-11-25 04:27.
  These are the first hours, not a long record; the hours below are from the image before, which
  differs in what it holds and not in how it builds.
- **The hour from 19:58 UTC**, 300 slots: 1,540 blocks built and 1,490 sent. Of the 50 not sent, 31
  paid no more than one already sent for the slot, 18 were for proposers no relay had a registration
  from, and one was too late. Every block sent was judged valid by reth's validator on the feeding
  machine.
- **What the relays said**: of 4,840 answers, 3,344 were 200, 1,495 were 202 and one post went
  unanswered in the 1.5 s allowed. None was a refusal. A 202 says the bid was below the relay's floor
  and the block was not checked, so only the 200s say a relay ran the block; the relays' lists mark
  these bids as not optimistic. In the hour before, on the image before this one: 3,465 of 3,468
  answered 200 or 202, three unanswered.
- **Timing**: in this hour no bid was answered after its slot began, and the last of a slot was in
  0.78 s before it at the median. In the hour before, two of 1,088 were answered after, the later by
  0.03 s. Five builds a slot, 1.15 s apart: 0.15 s for the request (1.5 MB) to arrive, 0.45 s to
  build, 0.07 s to post to four relays and have their answers, and the rest the feeder gathering
  transactions and proofs.
- **It began again by itself three times in six hours** (22:58 and 23:58 UTC on the 24th, 01:59 on
  the 25th), each time at a request to have a quote made, with nothing on its console. Every start
  draws new keys, so for three hours its bids at the relays were under keys this repository did not
  name. Bidding went on through each, some slots later. What set it off: the firmware keeps a timer
  interrupt going every 10 ms, and with one due while Google's host was making the quote, about one
  such call in ten never returned and the trust domain was started afresh. Why the host does that
  is not known here; a Linux guest, which does not run the firmware's timer, got 350 quotes of 350.
  The image now stops that timer for the call: 818 requests since on Google's machines, no start.
  The feeder, which asked every hour, asks once for each start.
- **No proposer took one**, and none was expected to.
- The machine costs about 23 cents an hour.

**On one machine** (Xeon Gold 6526Y; guest in TDX; a stand-in relay beside it):

- 1,000 slots in a row on the image now live as it was one small change earlier (its twin that knows
  the stand-in for its relay; the change after is to how a quote is asked for): every slot with a
  block sent, 6,790 blocks sent, every one judged valid by reth's validator and accepted by the
  stand-in, none late. Seven builds a slot, 0.75 s apart; 0.35 s of the guest's work for each.
- The same on the two images before it: 999 slots each (each run joined its first slot too late),
  7,017 and 6,415 blocks, all valid, none late.
- Three runs of 1,000 slots on earlier images: two with a block for every slot, one with 998.

**Against the blocks proposers took** (one machine, 875 slots, 2026-11-23): ours were worth 29% of
theirs at the median, and less summed, since their best blocks are far above their median. Ours held
94% by fees of what theirs held that was public a second before the slot. At real relays, in an
earlier hour, 18% at the median. Not measured from Google Cloud.

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
3. **The guest is this program, on Google's firmware.** Build the image and run the command in
   `docs/live/builder.txt`. `scripts/gce-check` asks five things: that the quote's signatures lead to
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
- The guest's port is open to the feeding machine alone, so you cannot ask it for a fresh quote
  yourself; the one in the repository is from when it started. A program that would stand between
  (`evm/builder/door`) is written and runs nowhere yet.
- A guest that starts again has new keys, and the record here is written by hand after a start.
  The feeder says when the two differ; until someone acts on that, the page names a key the guest
  no longer has, as it did for three hours on 2026-11-25.

## What is not done

- **It does not win.** No private order flow, no bundles, no blobs, nothing paid to the proposer beyond
  what the block earns. None of that is shown, and bundles and a payment signed inside would be new
  code inside.
- **It is not fast.** One core, one block at a time, about a second a round, and it stops 0.7 s short
  of the slot. Builders that win bid until the slot begins.
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
[jaune]: https://github.com/skbaek/jaune
[image-runs]: https://github.com/posix4e/cluck/actions/workflows/image.yml
