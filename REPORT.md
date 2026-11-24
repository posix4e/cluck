# A block builder in a trust domain, with far less inside it

A report on [`evm/`](evm/README.md), for people who build Ethereum blocks in trusted execution
environments. Written 2026-11-24. Every number here is from a run whose command and record are in
[TODO.md](TODO.md); what is weak is said here in short and in [THREAT_MODEL.md](THREAT_MODEL.md) at
length.

## The claim

A builder in a TEE asks whoever sends it transactions to trust everything inside the TEE. Today that is
a Linux image: a kernel, an init system, a C library, a TLS library, an execution client, the builder,
and whatever configures them at boot. BuilderNet's nodes, for one, are full Linux TDX images that hold
rbuilder, Reth, a proxy for order flow and one for attestation ([its release notes][bn] list them). Any
of it can read the transactions, so all of it is trusted.

This is a builder whose guest is one EFI program of 7.5 MB. Firmware starts it and it is compiled Lean
from there on. There is no kernel under it, no C library, no OpenSSL, no shell, no file system, and one
TCP port in. The network card's driver, Ethernet, IP, TCP, DNS, TLS 1.3, X.509, HTTP, the EVM, the
Merkle-Patricia trie, BLS signing, SSZ and the builder itself are Lean in that one program. The 0.4% of
it that is C reads nothing that comes from outside.

It runs today in a TDX trust domain on Google Cloud, builds a block about every second from the public
pool, signs its bids with a key that never leaves the trust domain, and posts them itself to Flashbots,
Ultrasound, Aestus and Titan, which accept them. Anyone can follow one of those bids from a relay's
public list back to the source it was built from; how is below.

It is not a competitive builder and does not claim to be. It sees only the public pool, and its blocks
are worth about a third of the winning ones. What it shows is that the trusted part of a builder can be
this small and still do the whole job, against the real chain and the real relays, where builders
already run.

## What is inside

The image as it runs on Google Cloud, counted from the linker's map (`scripts/image-inventory`):

| Part | Bytes | Share | Whose |
|---|---:|---:|---|
| Tables for placing the image in memory | 2,683,020 | 36.0% | the linker's |
| Jaune, an executable specification of the EVM in Lean | 1,505,013 | 20.2% | a third party's ([skbaek/jaune][jaune]) |
| The builder: engine, trie, TLS, bids, relays | 1,457,850 | 19.5% | this project's Lean |
| Lean's own library | 1,387,773 | 18.6% | Lean's |
| The OS: card drivers, Ethernet to TCP, DNS | 365,488 | 4.9% | this project's Lean |
| C | 30,580 | 0.4% | 2,875 lines printed from Lean's runtime, 1,250 written here |
| All, with start-up constants | 7,460,207 | | |

About 16,000 lines of Lean were written for it: 5,100 the OS, 5,000 the builder, 3,200 the execution
engine, 2,500 TLS and its cryptography. The C is the allocator and reference counting that compiled
Lean stands on, the entry from firmware, the page and register primitives the drivers call, and the TDX
calls for a report and a quote.

What that count leaves out or flatters:

- **Jaune is someone else's code** and a fifth of the image. Blocks are built by an engine written
  here and held to Jaune by tests, but Jaune's types, its decoding and its interpreter are still linked
  in, and what still calls them has not been looked at.
- **The compilers are trusted**: Lean's, and the C compiler and linker behind it.
- **Nothing proved covers the builder.** Parts of the runtime and the OS have proofs. The builder is
  tested: its cryptography against OpenSSL's, its engine against Ethereum's own suites (4,723 files)
  and against Jaune, its blocks against reth's validator. That is evidence, not proof.
- **Firmware is not in the count** and is far larger than the image. See the next section.

## What a relying party trusts

On Google Cloud:

1. **Intel**: the processor, the TDX module, the quoting enclave.
2. **Google's firmware.** It starts the guest, it is measured (MRTD), and Google signs a statement for
   that measurement, which is checked. What the firmware does is Google's word: nobody else builds
   it. On a machine of one's own the firmware can be built from source, as it is on the machine this
   was developed on, and replacing it with something small is the next reduction planned.
3. **The image**, measured into RTMR1, which anyone can work out from the image's file.
4. **Four certificate roots** the image holds for the relays' names, and every authority under them.

Not trusted: the host, the cloud's network, and the machine that feeds the builder. That machine runs an
ordinary node and hands the guest pending transactions, the parent block's header and proofs of the
state they touch; the guest checks every proof against the state root in that header. The feeder can
starve the builder, choose what it sees of the public pool, or have it build on a parent that is not
the chain's, which a relay's own check then refuses. It cannot have the builder sign for a block it did
not build, and it cannot read a transaction that was sealed to the guest.

## What it does

Each slot the guest is handed pending transactions and proofs, builds a block, signs the bid with a BLS
key drawn inside the guest, and posts block and bid to the relays over TLS connections of its own. It
does that again about once a second until shortly before the slot, each time with what has arrived
since.

A sender can also seal a transaction to a key the guest holds, so that the host that carries it never
sees it. Three blocks built this way are on mainnet (26463293, 26465583, 26470277). They won because a
test wallet paid the proposer, and they were built on one machine here, before Google Cloud.

## Numbers

**On Google Cloud** (`c3-standard-4` with TDX, us-central1), fed over the internet from a node 12 ms
away, bidding at four relays with nothing paid for a win:

- It has bid since 2026-11-24 18:30 UTC. These are the first hours, not a long record; the hours since
  are in `TODO.md` as they are read.
- **The hour from 19:58 UTC**, 300 slots: a bid sent in 296 (in the other four no relay had the
  proposer's registration). 1,540 blocks built, 1,490 sent, the rest kept back for paying no more than
  one already sent. Every block sent was judged valid by reth's validator on the feeding machine.
- **What the relays said**: of 4,840 answers, 4,839 were acceptances (200, or 202 for a bid below the
  relay's floor) and one post went unanswered in the 1.5 s allowed. No refusal. In the hour before,
  3,465 of 3,468, and three unanswered.
- **Timing**: no bid was answered after its slot began; the last of a slot was in 0.78 s before it at
  the median. Five builds a slot, 1.15 s apart: 0.15 s for the request (1.5 MB) to arrive, 0.45 s to
  build, 0.07 s to post to four relays and have their answers, and the rest the feeder gathering
  transactions and proofs.
- **No proposer took one**, and none was expected to.
- The machine costs 23 cents an hour.

**On one machine** (Xeon Gold 6526Y; guest in TDX; a stand-in relay beside it):

- 1,000 slots in a row on the image before this one: 999 with a block sent (the run joined the first
  too late), 6,415 blocks, every one judged valid by reth's validator, none late. Seven builds a slot;
  0.34 s of the guest's work for each, on a request of 2.6 MB.
- Three runs of 1,000 slots on earlier images, each with a block for every slot.
- 300 slots on the image now live: 2,041 blocks, all valid, none late.

**Against the blocks proposers took** (875 slots, 2026-11-23, one machine): ours were worth 29% of
theirs at the median, and held 94% by fees of what theirs held that was public a second before the
slot. The rest is order flow nobody gave this builder, and the last half second, which it does not use.

**How fast the parts are.** Building a block takes the guest 0.3 s on the machine it was developed on
and 0.5 s on Google's; reth imports a block in 0.04 s. A request of 2 MB crosses the internet into the
guest's TCP in 0.1 to 0.2 s. A post to four relays takes 0.09 s on connections the guest keeps open.

## Check it yourself

A relay lists every bid it is sent with the key that signed it. The guest says, in a TDX quote, that
the key is its own. So a bid can be followed back to source with nothing from us but this repository:

1. **The bid.** Ask a relay for the bids under the builder's key; [`evm/live/builder.txt`](evm/live/builder.txt)
   has the key and the link.
2. **The key is the guest's.** `evm/live/builder.quote` is the guest's answer to "what is your key",
   quoted by the machine it runs on.
3. **The guest is this program, on Google's firmware.** Build the image (`evm/scripts/build-efi tdx`)
   and run the command in `evm/live/builder.txt`. `scripts/gce-check` then asks four things: that the
   quote's signatures lead to Intel's root; that RTMR1 in it is what Google's firmware measures for
   that image file; that Google signed for the firmware in MRTD; and that the quote is of that key.
4. **The program is this source.** The image built here twice, in different directories and from
   nothing, is the same file. Its SHA-256 is in `evm/live/builder.txt`.

Where this is thinner than it looks:

- The image has only been built on one machine. Whether yours gives the same file is untried.
- RTMR0, the machine's configuration as the firmware measured it, was the same on every start seen
  and is not worked out from anything.
- The guest's port is open to the feeding machine alone, so you cannot ask it for a fresh quote
  yourself; the one in the repository is from when it started. A public page that does is next.
- Nothing looks for a quote or a firmware statement that has since been withdrawn.

## What is not done

- **It does not win.** No private order flow, no bundles, no blobs, nothing paid to the proposer beyond
  what the block earns. None of that needs more trusted code than is here; none of it is shown.
- **It is not fast.** One core, one block at a time, about a second a round, and it stops 0.7 s short
  of the slot. Builders that win bid until the slot begins.
- **One feeder, at somebody's home.** When that machine or its link stops, the builder stops.
- **Side channels.** The key's arithmetic was written to take the same steps whatever the key, and its
  machine code is read for that at every build. Nothing else has had that care, and what relays publish
  about each bid tells more about a sealed transaction than timing would.
- **Certificates** are not checked for revocation, and the date they are judged at is the host's word.
- **Young code.** The TCP was rewritten and the driver for Google's card written in the week of these
  numbers.

## Reproduce it

    git clone https://github.com/posix4e/cluck && cd cluck/evm
    # fetch mathlib's ready-made modules first: the command is in evm/README.md
    scripts/build-efi tdx                 # the image: .lake/build/efi/tdx/evm-os/BOOTX64.EFI
    scripts/run-fixtures tdx --key        # on a machine with TDX: starts it, asks, checks the answers

    # the same file on Google Cloud (see scripts/gce-try for what it needs), then fed from a node:
    SILO_GCE_BUCKET=... ../scripts/gce-try NAME .lake/build/efi/tdx/evm-os/BOOTX64.EFI 60
    builder/feed ADDRESS DIR --hold       # builds every slot and posts nothing; without --hold it bids

[bn]: https://buildernet.org/blog/2025/04/28/buildernet-v1.3
[jaune]: https://github.com/skbaek/jaune
