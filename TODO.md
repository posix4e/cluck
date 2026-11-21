# To do

What is done and what is left, in the order it has to happen. "Done" means it runs and something checks it;
where that something is only an emulator, the line says so.

## Intel TDX Ethernet guest

On 2026-11-18 the TDX EFI image booted on Intel hardware under Linux
7.0.0-14-generic and QEMU 10.2.1 with the two TDVF patches in `boot/efi/`.
The development EFI profile ran under QEMU TCG on an Arm Mac. The hardware
image refused to start in ordinary emulation.

- IPv4 hardware tests exercised concurrent TCP streams, the maximum 65,536-byte
  demo payload, random data, the reference self-test digest, half-close, rejection of
  invalid frame lengths, UDP echo and an 8,032-byte fragmented UDP datagram.
- An independent peer exercised IPv6 neighbor discovery, ICMPv6 echo, UDP and the
  framed TCP service over a QEMU point-to-point Ethernet link on real TDX.
- The DNS probe used the guest's resolver to obtain both A records for
  `ipv4only.arpa.` through QEMU on hardware. Native tests also exercised AAAA
  lookup, TCP retransmission, reassembly and the static next-hop cache.
- Intel QGS produced a 5,243-byte quote. Intel DCAP returned success with current
  collateral, matching verifier REPORTDATA and DEBUG clear. A fresh boot's quote
  matched the first boot's MRTD and all four RTMRs. The supplied verifier rejected
  a stale challenge and a mismatched RTMR1 policy. Verification in this test ran
  on the host. Application-level authentication and a deployment's own
  off-host measurement policy remain separate work.

| Tested binary | SHA-256 |
|---|---|
| TDX BOOTX64.EFI | `ddac15b56d362d845d3d029ad5a63b667cfe02538967fce5ca6d4782001b8159` |
| Patched combined TDVF | `1598169e86de5fe7feaf30ca5243d0fa9434396e82a7d672d905a7cded94ec83` |

The EFI image was rebuilt twice with the pinned Lean toolchain and produced the
same SHA-256 on the build machine. The network uses static addresses. DHCP, SLAAC,
TLS and a POSIX sockets interface are outside this implementation. Build and run
instructions are in [TDX.md](TDX.md).

## Ethereum block import, as a service (`evm/`)

An experiment: whether someone else's Lean, written for proofs and for Lean's own runtime, can be the service
on this OS. The Lean is Jaune, an executable specification of the EVM and of block validation with no
foreign code: upstream's `ba15f39` until 2026-11-20, and since then the branch `cluck` of `posix4e/jaune`,
four commits ahead of it (`evm/README.md`). The service takes a starting state, a genesis block and some blocks, and answers with
the tip hash and state root after importing them (`evm/README.md`).

On 2026-11-19 it ran three ways on one Intel machine under Linux 7.0.0-14-generic and QEMU 10.2.1: as a
process on Lean's runtime, as a process on the minimal runtime, and as an EFI guest in an Intel TDX trust
domain with the two TDVF patches in `boot/efi/`. The same guest built for development ran under QEMU's
emulated processor. No attestation was asked of it that day.

The requests are the Prague cases of five blockchain tests from `ethereum/tests` at `3129f16`. Each answer
was compared, byte for byte, with the fixture's own `lastblockhash` and the root of its `postState`. All
five agreed in all three places. Time is for the import alone:

| Fixture | Blocks | Gas used | Process, Lean's runtime | Process, minimal runtime | TDX guest |
|---|---:|---:|---:|---:|---:|
| highGasUsage | 11 | 0.23M | 47 ms | 146 ms | 112 ms |
| wallet2outOf3txsRevokeAndConfirmAgain | 8 | 1.7M | 43 ms | 115 ms | 89 ms |
| DelegateCallSpam | 1 | 8M | 451 ms | 575 ms | 439 ms |
| walletReorganizeOwners | 259 | 38M | 2.6 s | 4.7 s | 4.6 s |
| ShanghaiLove | 1 | 4.5M | 38.4 s | 38.9 s | 39.0 s |

The process columns were measured before the merge that brought the arithmetic proofs, the TDX column
after it. Under the emulated processor four of the five were run and agreed (56 s for the 259 blocks);
`ShanghaiLove` was not run there.

- A request with one byte changed inside its last block is answered with status 3 after seven of eight
  blocks, one with a byte changed in an account's balance with status 2, and one cut short with status 5,
  on both runtimes as processes. These three were not sent to a guest.
- The TDX image is 3 MB and came out byte for byte the same from two builds on that machine. The guest is up
  about four seconds after QEMU starts. The patched firmware built there has the SHA-256 recorded in the
  section above.
- `ShanghaiLove` is a replay of the 2016 attack that made cheap operations expensive for clients. It takes
  Jaune 39 seconds for 4.5M gas on either runtime, so the time a block takes is not bounded by its gas.
- The benchmark (`evm/Bench.lean`), minimal runtime against Lean's, over four runs of each whose times
  spread widely on a machine doing other work: 2.3 to 3.3 million simple opcodes a second against 3.4 to
  4.6; 256-bit `mulmod` 3.1 to 4.3 µs against 2.2 to 3.1; one bn254 pairing 2.1 to 2.9 s against 0.6 to 0.8;
  twenty `ecrecover` attempts 83 to 117 ms against 15 to 21; a 2048-bit `modexp` 79 to 112 ms against 2 to
  4. The big-number work is slower because the minimal runtime's arithmetic is Lean on 32-bit limbs where
  Lean's own runtime calls GMP. Both runtimes computed the same results every time.

On 2026-11-20 the TDX guest answered attested requests (`evm/Evm/Attest.lean`): the response, then a
TDREPORT whose REPORTDATA is the SHA-256 of a 32-byte challenge and the request, then the SHA-256 of the
response. This host's Intel QGS turned each report into a 5,243-byte version 4 quote.

- `evm/demo/test-verify.mjs`, under Node 25, checked three quotes with `evm/demo/verify.js`: the quote's
  signature, the quoting enclave's endorsement of the attestation key, that enclave's signer against Intel's
  published TD_QE identity, its report against the PCK certificate, the chain to Intel's SGX root key, the
  DEBUG attribute clear, and REPORTDATA against hashes computed by the client. It refused the same quote
  with one byte changed in each of eleven places and with the clock set to 2060. Intel's DCAP library was
  not run on these quotes: it is not installed on this host. TCB status and revocation were not checked.
- The three requests were a fixture as it is (status 0, the fixture's answer), with one bit changed in the
  state root its last block's header claims (status 3 after ten of eleven blocks), and with one bit changed
  in an account's starting balance (status 2).
- Two boots of the image with SHA-256 `9c694a30d3002158554911f3e142b754353af9b8aa99ebdf20ca3eddd4fed369`
  gave the same measurements: MRTD `d316047a…4188a7`, RTMR0 `32b983e0…09da10`, RTMR1 `85029e71…89f5e5`,
  RTMR2 and RTMR3 zero. Nobody has derived those from the image and firmware without booting them.
  A fresh clone of commit `4c3cf93` built the same image.
- The page (`evm/demo/`) ran the same checks in headless Chrome 154 at desktop and phone widths, and the
  five fixtures gave the fixture's answer through it. It has been served on loopback and, behind an HTTPS
  proxy, to the operator's private network; it has not faced the internet.

On 2026-11-20 the service answered about blocks of mainnet, as a process on Lean's own runtime, from a
witness instead of the state (`evm/Evm/Stateless.lean`, `evm/Evm/Trie.lean`). The witnesses came from reth
2.11.0 following mainnet on the same machine (`evm/witness/fetch`).

- 21 consecutive blocks, 26456375 to 26456395: 19 were answered valid with the block hash and state root
  the node reports, in 1.7 to 12.5 seconds each; the largest had 544 transactions and 45.6M gas. 2 were
  answered with status 6, the witness falling short of an account the block read. None was answered with
  a verdict the node disagrees with.
- `stateless-test`: every block of four fixtures (279 blocks), with a witness cut from the whole state,
  gets the answer the import with the whole state gives. For three of them every node, key and code of
  every block's witness was then left out in turn: of 1,143 shortened witnesses, 560 were answered with no
  verdict (status 6 or 8) and 583 with the same answer as before; none with a different one. A block whose
  header claims a wrong state root was answered invalid.
- That test found three ways a read went unrecorded and a wrong verdict came out, each now closed: Jaune
  dropped the read sets of every transaction before Amsterdam; nothing recorded what is read in preparing
  a transaction; and a payment to an account left out of the witness looked like the making of a new one.
- `trie-test`: 9,900 random writes and removals in five shapes of trie agree with Jaune's root, through
  whole and partial witnesses, with 14 malformed node encodings refused.
- The three stateless fixtures in `evm/fixtures/stateless/` get their answers as processes on both
  runtimes. In a TDX guest built from the same source (image SHA-256
  `78571353b486874dceff57fcd6527568079f985d7b1f4a157e2a623ba8fcaadc`) they and four of the whole-state
  fixtures got their answers too; the whole-state ones took 126 ms to 6.4 s there against 87 ms to 4.5 s
  the day before, on a machine now also running a node, and how much of that is the reads being recorded
  has not been separated out.
- Before the jump-destination check was replaced, one mainnet block ran for ten minutes without finishing,
  99.9% of it in Jaune's `noPushBefore`.

Later the same day the service answered about blocks of mainnet from inside the TDX guest.

- 100 consecutive blocks, 26458315 to 26458414 (66 to 625 transactions, 6.3M to 60.0M gas, requests of
  1.9 to 21.7 MB): as a process on Lean's own runtime, and then in the TDX guest (image SHA-256
  `62a005f3…db12309`, one boot, one after another), every one was answered valid with the block hash and
  state root the node reports. In the guest a block took 1.8 to 70.5 seconds, median 10.8, 4 of them
  under 3 seconds and 41 under 10; the request took a further 0.2 to 2.2 seconds to arrive, median 0.9.
  Two profiles of the service as a process were being taken on the same machine for part of that run.
- The 21 blocks above, in the guest: all valid, 2.7 to 36.6 seconds; and all valid again on the image
  this source builds (SHA-256 `aabff013…c43233e1`), which differs from the one the 100 were put to by
  the limit on what is held of unfinished requests. One mainnet block (the smallest, 1.9 MB) was put to
  the emulated guest and was valid, in 22 seconds. The two that had fallen short now
  have the address they lacked (`evm/witness/fetch` adds what the service says is missing and tries
  again; it had to for 4 of the 100).
- The guest's runtime, not the guest, is what is slow: as processes, three of those blocks took 26.0, 28.6
  and 13.0 seconds on the minimal runtime against 10.2, 10.9 and 4.4 on Lean's own, and 31.7, 36.6 and
  15.7 in the guest.
- Where the time goes, from a profile of the 21 blocks as a process on the minimal runtime (310 seconds in
  all): 40% in the final exponentiation and Frobenius maps of the bn254 pairing, which Jaune computes as
  plain powers in the extension field; 26% in recovering senders' addresses from signatures; 13% in
  checking jump destinations, a pass over the contract from its start for every jump; 11% in the rest of
  the interpreter; 4% in the witness and trie; 3% in the rest of the pairing; 2% in BLS12-381. Almost all
  of the first two is arithmetic on numbers of 254 and 256 bits, which the minimal runtime does in Lean
  on arrays of 32-bit limbs with a division for every reduction.
- A request arrives at about 8.5 MB a second. It was 5.5 before the wait for the network device to hand
  back a transmit buffer (`boot/efi/platform.c`) was preceded by asking for it again at once, which is
  what each acknowledgement was waiting on. A TCP window of 64 KiB instead of 8 changed nothing, before
  that or after, and was not kept.
- `scripts/run-fixtures tdx --limits`: a frame one byte over the 32 MiB accepted is closed; of two
  clients each part way through a request, the one that would take what is held past 40 MiB is closed;
  a fixture is answered afterwards.
- `ShanghaiLove`, which took 39 seconds when it was first run (above), takes 0.2 since the jump-destination
  check was replaced, on both runtimes and in the guest, with the same answer.
- Not tried: a request of the full 32 MiB (the largest was 21.7 MB, and as a process on the minimal
  runtime that block's peak was 183 MB of a heap that is 256 MiB in the guest); mainnet blocks on the
  emulated processor beyond the smallest of them; more than one boot; a build of the image from a fresh
  clone.

That evening the three largest items of that profile were taken off it, in this package's branch of Jaune
(`posix4e/jaune` at `6143c7b`): the bn254 pairing check makes one final exponentiation, by the split into
an easy and a hard part, where it made a plain power for every pair; the jump-destination check goes back
from the destination to a position that must start an instruction, where it walked the contract from its
start; and senders are recovered over a field of ten 26-bit limbs in machine words, where every
multiplication was a product and a division of big numbers.

- The 100 blocks as a process on the minimal runtime: median 10.4 seconds before, 7.6 with the first two
  changes, 3.65 with all three (mean 12.3 to 4.0, slowest 65 to 21). On Lean's own runtime: 5.4, 3.1,
  2.5. Every answer the node's at each step.
- The 100 blocks in the TDX guest (image SHA-256 `fa2bc573…25af4ef9`): all valid, 0.6 to 25.3 seconds,
  median 4.6 where it was 10.8, 21 under 3 seconds and 95 under 10. The 21 blocks: all valid, 1.0 to 9.8,
  median 3.9. The machine was building and testing other things for the whole of that run, so the guest
  may be faster than this says; it is not yet known to be.
- The test chains in the guest: `walletReorganizeOwners` 2.3 seconds where it was 5.6 (and about 3.1 on
  every run since, with no change between that would explain it; as a process it is 3.0 on every build
  after the first), `highGasUsage` 0.02 where it was 0.15.
- Each change was held to Jaune's own gates on the branch, none of which had been run there before: its
  Osaka (2,333 files), Prague (2,341) and BPO2 (11) suites of `tests@v21.0.2`, its 76 transition-tool
  cases, its curve oracle (596 cases, 23 of them now put to the new recovery), and its layering and
  hygiene checks. All pass. The hygiene check passes because the unproved jump check is now on its list
  of exceptions with the reasons, not because it was proved.
- `evm-test` compares the two substitutions with what they stand in for: 26,784 positions of made-up
  code, some of it all pushes so that the check has to give up looking back, and 3,000 made-up signatures,
  1,536 of which have a key.
- Then this package's own witness and trie code (`evm/Evm/Trie.lean`, `evm/Evm/Stateless.lean`): the
  32-byte words of a node are read where they lie, not cut out and made lists; the maps of hashes are
  ordered by comparing four machine words; and the state root after a block no longer joins the lists of
  accounts and of slots before and after and searches the result for repeats, which cost the square of
  what the witness held. In the TDX guest with that (image SHA-256 `44d221a2…eb6b8ff6`), on a machine
  doing nothing else but following the chain: the 100 blocks all valid, 0.4 to 24.5 seconds, median 3.9,
  29 under 3 seconds and 95 under 10; the 21 all valid, 0.8 to 6.9, median 2.6; `--limits` as before.
  One block put to the same guest five times among 35 others took 7.2, 7.8, 6.3, 8.3 and 6.2 seconds:
  no steady slowing as the guest serves, and a spread of a quarter that has not been explained.
- Then how Jaune's interpreter holds its state (`posix4e/jaune` at `69db932`, four more commits, each
  proved equal to what it replaces and held to the same gates). Every write to EVM memory was copying
  all of memory and freeing the copy it replaced: the loop that runs instructions kept the machine
  record through each step in order to read one field of it afterwards, and the wrappers around each
  instruction kept the state they had handed it, so the state always had two owners and nothing in it
  could be written where it lay. The loop now takes the record apart first and the wrappers have compiled
  forms that do the same. Two smaller changes went in with it (memory grows where it lies, and a
  polynomial division no longer inverts a leading coefficient of one), neither of which could be seen in
  the times on its own.
  - The 100 blocks as a process on the minimal runtime: median 2.58 seconds where it was 3.4, mean 3.0,
    slowest 21, 59 under 3 seconds. The worst block for memory went from 8.2 seconds to 4.4.
  - In the TDX guest (image SHA-256 `68228fdf…b6ac064c`), on a machine doing nothing else but following
    the chain, one run: the 100 blocks all valid, 0.4 to 19.0 seconds, **median 2.99**, mean 3.5, 51 under
    3 seconds and 99 under 10; the 21 all valid, 0.7 to 6.5, median 2.8; `--limits` as before. That is
    the line this was working towards, reached with nothing to spare and on one run.
- Where the time went before that last change, from a profile of 33 of the 100 blocks as a process on the minimal runtime:
  50% in the interpreter and the rest of Jaune, 18% in this package's own witness and trie code, 6% in
  sender recovery, 5% each in BLS12-381, keccak and the bn254 Miller loop, 3% in the bn254 final power,
  2% in the jump check. Counted another way, 35% of it is the minimal runtime allocating and freeing
  (issue #1), and 7% is one function of Jaune's that grows EVM memory an element at a time.

On 2026-11-21 the aim changed. It had been the check a relay makes of a builder's block. It is now the
builder: a block built inside the guest, bid for with a key that never leaves it, delivered by a relay and
landed on mainnet; and only after that a faster engine in place of Jaune. (What Flashbots itself keeps in a
trust domain is its builder, in a Linux machine; relays and mev-boost are not in one.)

The first piece of that is done: the guest builds a block (`evm/Evm/Build.lean`).

- The 21 mainnet blocks above, each built again from its own transactions in their order, as a process on
  both runtimes and in the TDX guest (image SHA-256 `c525a02d…3cc30138`): every one came out with the hash
  and the state root the chain has for it, which is every field of the header. In the guest that took 0.8
  to 8.4 seconds a block.
- The same blocks with their transactions ordered by what they pay, as a process: every block built was
  one `Evm.Stateless` accepts. Between 2 and 13 of each block's transactions were left out, 122 of 5,842
  in all: 51 because they carry blobs, and the other 71 for reasons not looked at one by one (rejected in
  the new order, or reading something the witness made for the old order does not prove).
- `build-test` on three test chains: built again as given, each is the block it was; a transaction proposed
  twice is left out the second time; and of 404 witnesses with one piece missing, 110 built nothing, 74
  built a smaller block, and none built a block the checker refuses.
- A witness for transactions that are not in a block yet can come from the node's proofs at the head:
  for everything one full block touched (545 accounts, 1,558 slots) reth answered in 0.8 to 1.2 seconds
  over 16 to 32 connections, 3 MB of nodes. Those proofs do not include the neighbour a trie needs when a
  slot is cleared and its branch collapses; about one transaction in nine clears a slot, and a block that
  needs such a node is answered with status 6.
- The arithmetic for a signing key is written (`evm/Evm/Sign/`), with no key yet and nothing calling it:
  BLS12-381 on fixed-width words, a secret deciding no branch. `bls-test`: 54,850 field operations against
  `Nat`, 242 sums of points against Jaune's, and the public keys and signatures of 23 keys byte for byte
  those `JauneConsensus` makes with the key as a number. The key's part of a signature takes 8 ms as a
  process on Lean's runtime; hashing the message to a point, which is public and still Jaune's, takes 29.
  What is and is not known about its timing is in `THREAT_MODEL.md`.
- **A hole in the checker, found by the builder, and closed.** The first blocks built from pending
  transactions were put to reth's own validator (below), and it refused one: the guest had run a
  transaction for less gas than the node did. The cause was in the checker as much as the builder. Before
  Amsterdam, Jaune records nothing of the account a contract calls, so an account the witness left out
  and that only a contract's call reached was taken for empty, unnoticed. One mainnet block (26456381)
  with each of 77 addresses left out of its witness in turn: the code as it stood answered "invalid" 32
  times, for a valid block. What was written above on 2026-11-20, that no shortened witness was answered
  wrongly, was true of the test chains it was run on and false of mainnet. Both reads are now recorded
  (`posix4e/jaune`, in the compiled form of `accessDelegation`, unproved and said to be), and
  `stateless-test real` and `build-test real` leave addresses out of real blocks' witnesses: 225 witnesses
  of three mainnet blocks, none answered wrongly, 216 with no verdict; 114 for the builder, every block
  built one the checker accepts with the whole witness.
- Building from pending transactions, in shadow (`evm/builder/shadow`): each slot the host takes pending
  transactions from reth's pool, has reth trace them and prove the state they touch at the parent block,
  puts them to the guest, and hands what is built to `flashbots_validateBuilderSubmissionV5` on the same
  node, which is the code relays run. Nothing is signed or sent. First runs, as a process: of 25 slots, 21
  built a block the node judged valid, each ready 6.6 to 9.7 seconds before its slot, and the randomness
  and withdrawals guessed for the slot were the next block's every time; the rest were slots lost to the
  host (the head moving under it) or a witness too short for the block as a whole.
- **The guest holds a key and signs bids** (`evm/Evm/Bid.lean`, `drawKey` in `evm/EfiMain.lean`). In the
  TDX guest (image SHA-256 `c7415c05…54f1913d`): the builder's key asked for twice was the same key; a
  bid for a block built from a fixture came back in 0.47 seconds signed by it, and `bid-verify`, outside,
  found the signature good by `JauneConsensus`'s verification; the fixtures and `--limits` as before.
  `bls-test`: a bid's root and domain are `JauneConsensus`'s, and a registration that a validator signed
  for a relay on mainnet verifies under the same domain, which is the evidence that a mainnet relay would
  read these signatures as it reads its validators'. `scripts/check-secret-code tdx`: in the image's own
  machine code the field's product, sum and reduction have no conditional jump and no division.
- **Bids for blocks built from pending transactions, in the guest, in shadow.** A first run of 182 slots
  (image `6f26eddb…6b5966`, no key yet): 177 built a block the node's validator judged valid, with the
  slot's randomness and withdrawals guessed right every time; 4 were lost to the node refusing a proof and
  1 to a transaction that creates a contract (since left out one at a time); one block was ready 1.7
  seconds before its slot and every other at least 2. The guest took 0.17 seconds at the median and 4.8 at
  the most. Blocks were small, a median of 0.85M gas, because little is pending in public.
- **What a win would cost.** Over 160 of those slots, the bid that won (relays' public data) was 0.0081 ETH
  at the median and the guest's would have been 0.00016: short by 0.0054 ETH or less in a quarter of
  slots, 0.0073 at the median, 0.0195 or less in three quarters, and 2.2 at the most.
- **A top-up, tried against the node's validator only.** `builder/shadow --top-up` puts a transaction from
  a wallet on the host in front of what is proposed. At first it was a transfer to itself with a large
  tip (four slots as a process with 0.001 ETH, each bid worth that much more, each block judged valid by
  the validator, which checks that the proposer is paid what the bid says). That one was a payment to
  whoever put it in a block, in any slot, for as long as its nonce was unused, and every relay sent a
  block would have held a copy. It is now a transaction that pays the block's fee recipient only in a
  block with the slot's number and the proposer's fee recipient, and reverts anywhere else, at the cost
  of its gas (53,892 on the node, at 2 gwei over the base fee). On the node: with the right number and
  recipient the recipient gained the amount, and with either wrong it reverted. Four slots as a process
  with 0.001 ETH: each bid was worth that much more and each block was judged valid. Nothing was sent to
  a relay and the wallet's balance did not change. What it does not close: someone who sees the block
  within its slot and builds another for the same proposer with the proposer as fee recipient could use
  it, which is a relay or its builder turning on a builder, and is what every builder trusts a relay not
  to do.
- **1,300 slots with the key in the guest, and the line not reached** (2026-11-21, TDX, image
  `df9f34be…74dc64fe`, one key throughout, 8M gas asked for). 1,045 slots built a block; the node's
  validator judged all 1,045 valid and none was refused, every one was signed and `bid-verify` found every
  signature good, and the slot's randomness and withdrawals were guessed right 1,043 times of 1,043. The
  longest run of valid, signed blocks each ready two seconds before its slot was 790, not 1,000, broken
  twice, and neither time by a wrong block:
  - One block (6.5M gas, 41 transactions) took the guest 9.3 seconds and came back 3.8 seconds after its
    slot began; its parent had arrived 5.8 seconds into its own slot. The guest's time for a block was 0.29
    seconds at the median, and over 2 seconds in 20 slots. Since then a request for a bid names the time it
    allows, and the guest ends the block with what is in it when that is up (`JBID2`; `Stage.finishWith`
    in `evm/Evm/Build.lean`): a slow block becomes a smaller one. The request that was slow was not kept,
    so what in it was slow is not known; the host now keeps any request that takes over 2 seconds.
  - For 255 slots in a row the guest built nothing, rightly: the chain replaced block 26461713 with
    another, the host went on sending the header it had kept under that number, and the guest refused
    headers that are no chain to the parent (status 5) until the stale one left the window of 255. The
    fault was the host's (`builder/shadow`), which now follows headers back from the head by parent hash.
    After it the last 188 slots were all valid, signed and in time.
  What a win would cost, again, over the 189 of these slots whose winning bid the relays' public data
  still gave: the winning bid 0.0099 ETH at the median, the guest's 0.0002; short by 0.0067 or less in a
  quarter of slots, 0.0097 at the median, 0.2746 at the most.
- **A second run, 789 slots, and the line again not reached** (2026-11-21, TDX, image `346c4ffd…61df038a`,
  with the time limit and the host following headers by parent hash; stopped by hand at 789 of 1,300 once
  it could no longer reach the line). 765 slots built a block: all 765 judged valid by the node's
  validator, all signed, none late (the closest was ready 3.1 seconds before its slot, the median 8.9),
  the slot's randomness and withdrawals right 764 times of 764. The guest took 0.24 seconds at the median
  and 2.51 at the most, over 2 seconds in 8 slots, whose requests are kept. 24 slots built nothing, and
  the longest run of good slots was 109: a transaction that stayed in the pool touches one contract
  (`0x06450dee…599a6fb8`) at more than 1,024 storage slots, the node proves at most 1,024 slots of an
  account in one call, and the host gave the slot up. The fault was the host's again; it now asks in
  pieces and joins them (`SHADOW_PROOF_KEYS`), checked by forcing pieces of 8 for eight slots in TDX, all
  valid. So in two runs 1,810 blocks were built, none wrong, and every break of the line but one late
  block was a slot with no block. **1,000 in a row has not been shown**, and it was decided on 2026-11-21
  to go to the relays without a third run: a slot with no block sends nothing, and no block is sent that
  the node's validator has not judged valid. What a win would cost, over 283 of these slots that one of
  the four relays delivered: the winning bid 0.0076 ETH at the median; a top-up of 0.01 ETH would have
  beaten it in 66% of them, 0.015 in 81%, 0.02 in 87%, 0.03 in 91%, 0.05 in 95%.
- **A dry run of what is to go live found the guest ended by its own large requests** (2026-11-21, 100
  slots in TDX with a report asked for each bid and the 0.02 ETH payment in each block, nothing sent). 97
  slots built a block, all valid and signed, the payment in every one built for a registered proposer.
  Three slots got no answer: each request was over 4 MB (the contract with over 1,024 slots again, now
  that the host can prove it), and with a report asked for the guest hashed it as a list of bytes, which
  the 256 MiB heap does not hold; the guest stopped and the host started another, with another key. The
  same requests without a report took under a second. The report's hash now walks the bytes where they
  lie (`Evm.Attest.sha256`, tested against Jaune's and the standard, not proved), and the three requests
  are answered with a report in about a second each in TDX (image `05169195…92fdac45`), the report's data
  checked against another SHA-256. Still so: a 21.7 MB block request with a report ends the guest (memory
  again: a report holds two more copies of the request); a guest out of memory stops instead of refusing;
  and after a slot nobody proposed the host builds for a slot already past (one such block here, empty and
  1.9 seconds late, which would not have been sent).
- **The payment cannot be made twice.** Every payment a run signs carries the transaction count the
  wallet had when the run began, and the run ends when the chain's count has moved, whether or not it saw
  its own block land; it also looks for its block at its number, not only as the head. Tried as a process
  against a stand-in relay with a stand-in for the node that reported the count moved: the run sent its
  bid and stopped at the next slot.
- **A block built in the guest is on mainnet** (2026-11-21 11:50:59 UTC). Block 26463293, slot 15703153,
  hash `0xb24cccb2e34a33014f6b0509ad980f7ae67d558e3a1a157e55602db5b509382b`, 20 transactions, 871,663
  gas, extra data `cluck`; built in the TDX guest (image `05169195…92fdac45`, commit `cf1ee2d`, tree
  clean) in 0.31 seconds and sent 7.1 seconds before its slot. The bid was signed by the key the guest drew
  at that start (`0xa5eaab83…e2dfc12c`), which went with the guest when the run ended. After a second
  dry run of 100 slots on that image (100 blocks, all valid and signed, the payment in each of the 91 for
  a registered proposer), the live run sent one bid in all: its first slot was built late (the first after
  a start, the parent 11.7 seconds old) and not sent; its second went to Flashbots, Ultra Sound, Aestus
  and Titan, each answered 200, and the proposer took it. Flashbots, Aestus and Titan list the block as
  delivered under the guest's key; Ultra Sound took the bid and lists no delivery for the slot. The bid
  was 0.02013 ETH, of which 0.02 was the payment (`0xd1b5a717…f2d130c7`, last in the block, 61,828 gas);
  the best bid from anyone else was 0.0076. The wallet went from 0.2881772635 to 0.2681681779 ETH: the
  0.02 and 0.0000090856 of gas, once, and the run stopped itself. The request, reply, report and quote
  are kept (`/data/eth/shadow/landed/`); `demo/test-built.mjs` finds the quote good, for that request and
  that reply, challenge the parent's hash, and refuses seven changed copies; `demo/built.html` shows it.
  What it does not show: that the builder can win a slot on what its block earns (it paid 0.02 to win
  0.0001 of fees), that it can do so twice, or anything about order privacy. Not looked at: the page in a
  real browser. Not done: the kept files are not published anywhere public. The chain had finalized the
  block by 12:06 UTC, with the same hash.
- **Sending bids, as it stood before the block above.** `builder/shadow --live --relays …` posts each
  bid to the relays named, and only a block the node's validator judged valid, signed, before its slot, to
  relays that hold the registration it was built for; it asks the guest for a report with each answer
  (the challenge is the parent's hash), stops at the first block built here that becomes the chain's
  head, and keeps the request, reply, report and quote for it. Tried as a process against a stand-in
  relay on the same machine: four slots, four bids posted in the builder API's shape, the stand-in's
  "payload attributes not yet known" answered by asking again. Then in a TDX guest with `--attest` and no
  relay: three slots, each bid with a report, and the last kept with the quote the host's quoting service
  made of it; `demo/test-built.mjs` found the quote good, for that request and that reply, with the
  parent's hash as its challenge, and refused the set with any one of seven bytes changed. `demo/built.html`
  is the page for it, run so far only against a stand-in for a browser. Not run: noticing a landed block,
  and any real relay. From the relays' documentation and code, read on
  2026-11-21: Flashbots, Ultra Sound, Aestus and Titan take bids from a key they have not seen (as
  low-priority, fully simulated); bloXroute wants a paid plan; a bid below a relay's floor is skipped, not
  refused, and Flashbots drops an empty block without saying so.
- Not done: 1,000 slots in a row with a valid block ready in time (two runs fell short, above); a second
  landed block, or one that wins without a payment on top; the report that ties the key to the image has
  not been fetched by anything outside (the kept quote covers the reply, which holds the key, and is not
  published); the order privacy a builder in a trust domain is for: transactions still reach the guest in
  the clear, through the host.

What is next, in order:

1. **Building in shadow.** A program on the host follows the chain and each slot puts pending transactions
   and their proofs to the guest; reth's own validator (the code relays run) judges each block built.
   Nothing is signed or sent. The line: 1,000 slots in a row with a valid block, each ready two seconds
   before its slot.
2. **A key that never leaves the guest.** BLS12-381 signing on fixed-width words with no branch on the
   key, held to the existing verification and to known vectors, and its machine code read for jumps that
   depend on the key. The guest signs bids for blocks it has just built and nothing else.
3. **What a win costs.** A day of comparing the bid the guest would have made with the bid that won.
4. **Live.** A top-up signed outside the guest, submission to relays, one block landed, its quote shown.
5. **A faster engine** in place of Jaune, tested against it.

Steps 2 to 4 are done as far as one block (above); step 1's line of 1,000 was not reached and was passed
over by decision. Step 5 is what is next. Its mark, read from the node's own log on this machine
(2026-11-20 to 21, 3,186 blocks as they arrived, not the 121 saved ones, which the log no longer holds):
reth takes 43 ms for a block at the median (28.6M gas, about 640M gas a second), 88 ms at the ninetieth
percentile and 0.6 seconds at the most, outside a trust domain and with its caches warm. The guest takes
3.0 seconds at the median for a block of the same chain, about seventy times as long.

The faster engine (`evm/Fast/`), step by step:

- **How it holds its stack is settled, by trial** (`evm/Fast/Spike.lean`, 2026-11-21). The benchmark's
  loop of eight instructions (PUSH, ADD, DUP, GT, JUMPI) written as one loop whose stack, stack pointer,
  program counter and gas are arguments of their own, in two layouts. On the minimal runtime, 80 million
  instructions: the stack as bytes, 32 to a word, 0.85 seconds (94 million a second); as 32-bit limbs in
  an array, 1.45 seconds (55 million a second). Jaune runs the same loop at 3.1 million a second, and
  both layouts end with the gas and stack Jaune ends with. Bytes it is. The loop's generated C allocates
  only when it halts, its dispatch is a jump table in the object code, and it links against the minimal
  runtime with no function added. What this is not: an engine. Eight instructions, one frame, no memory,
  no state, and an instruction is only a small part of what a block costs. Bounds are still checked
  through `Nat`, which costs a little and can go.
- **Keccak-256 on 25 machine words in variables** (`evm/Fast/Keccak.lean`), the permutation and the sponge
  as one loop reading the input where it lies. Against Jaune's on the minimal runtime: 200,000 hashes of
  32 bytes in 0.11 seconds for 0.42 (3.7 times), 50,000 of 532 bytes in 0.10 for 0.29 (2.9 times). The mark
  set for it was 5 times and it was not reached: Jaune's was less slow than supposed, and at about half a
  microsecond a block this is near what the processor does in C. `evm-test` holds it to Jaune's on 614
  inputs. The witness trie uses it now (`Evm.Trie.hashOf`): `trie-test`, `stateless-test`, `build-test`
  pass, and the 21 saved blocks as a process on the minimal runtime give the same 21 answers in 61.6
  seconds for 65.0 (two runs each), about 5% less. Not rebuilt or run: the TDX image, and the guest.
- **The 256-bit word and its arithmetic** (`evm/Fast/Word.lean`, `evm/Fast/Wide.lean`): four machine
  words; add, subtract, compare, the bitwise and shift operations, BYTE, SIGNEXTEND, CLZ, multiply and EXP
  with no division and no allocation when inlined; DIV, MOD, SDIV, SMOD, ADDMOD and MULMOD by Knuth's long
  division on 32-bit digits (there is no 128-bit multiply or divide to call). `fast-word-test` puts every
  operation through `Nat`'s answer: 29 awkward values and 400 drawn in several shapes, every pair for the
  operations of two (193,050 cases each) and 910,389 triples for the two of three, 5.9 million cases, all
  agreeing, with the same output on Lean's runtime and the minimal one. On the minimal runtime 200,000
  MULMODs take 0.21 seconds for Jaune's 0.89. A first version of the division, written with `for` loops,
  was right and slower than Jaune's, because such a loop builds a tuple at every turn: loops in this
  engine are functions that call themselves. Nothing here is proved.
- **The interpreter** (`evm/Fast/State.lean`, `Machine.lean`, `Interp.lean`): every instruction of Prague
  and Osaka; calls and creations as the loop running itself again on one shared stack; memory as bytes;
  accounts and storage fetched from what stands behind the first time they are touched, changed in place,
  and undone by a journal. `fast-op-test` runs programs through it and through Jaune's interpreter and
  compares how each ends, the gas left and the bytes returned: 166,566 programs of one arithmetic,
  comparison or bitwise instruction on awkward and random operands, and 3,000 programs of 20 to 200
  instructions drawn at random from those that need no world (stack, arithmetic, memory, input, code),
  each returning four words of its stack and a kilobyte of its memory. All agree. On the minimal runtime
  the benchmark's loop runs at 39 million instructions a second for Jaune's 3.1 million; the trial did 94
  million, and why the whole loop is 2.4 times slower than the trial is not found (the profiler needs a
  setting only root can change). Two things found on the way and kept as rules: a function handed to a
  helper from inside the loop was built before every instruction, so calls are made ready and settled
  outside the loop and run by the loop itself; and where two ways of computing a word meet again the word
  is built as an object, so such values are handed on as four numbers. **Not tested at all yet:**
  anything that needs a world or a second call (storage, balances, CALL, CREATE, logs, SELFDESTRUCT,
  precompiles), jumps, running out of gas, and the stack's limits; nothing proves anything; and nothing
  uses it. An empty account that is touched is not removed (EIP-161), which mainnet no longer needs and
  some tests do.
- **121 blocks of mainnet through the new engine, each as its header has it, state root and all**
  (2026-11-21; `evm/Fast/Tx.lean`, `Fast/Block.lean`, `Evm/Bridge.lean`, `fast-replay`). Transactions
  (what one may be and what it pays, access lists, blobs, set-code authorizations, creation, refunds, the
  floor price) and blocks (the two calls a block makes before its transactions, withdrawals, deposits read
  from logs, the two request queues) are written on the engine. `fast-replay` runs a saved block on the
  state its witness gives and compares five things with the block's own header: gas used, the root of
  the receipts (every transaction's success, gas and logs), the bloom of the logs, the hash of the
  requests, and the root of the state afterwards, which is worked out from the engine's world on this
  package's trie after checking that everything the engine fetched was supplied or proven absent. All
  121 saved blocks (26456375 to 26456395 and 26458315 to 26458414, up to 625 transactions and 60M gas)
  agree on all five, on the witnesses as they were saved.
  - The first four agreed the first time they were run. The state root was added after, and 29 blocks
    then failed, not on the root but on the check of what was fetched: the engine had fetched accounts
    for which the witness holds no proof at all. It fetched an account or slot before finding that the
    instruction could not pay for it; a node, finding there is not the gas for a cold read, does not
    read. The answer was the same either way (out of gas), but an engine that reads what it cannot pay
    for asks a witness for more than a node will give. It now prices a read from whether the address or
    slot is warm, which needs no fetch, and fetches only what it can pay for. `fast-replay --where
    ADDRESS REQUEST` is what found it: it names the transaction that first fetches an account and what
    the witness holds for it.
  - Times, on Lean's runtime, at the median of the 121: reading the witness 105 ms, recovering senders
    149 ms, the block 234 ms (48 ms to 3.8 seconds), the state root 132 ms; 651 ms for the four. As
    whole processes on the 21 blocks: 16.6 seconds through the engine for 36.1 through Jaune
    (`evm-serve`), 2.2 times. The process through the engine also does things the service will not need
    it to (the receipts root by Jaune's slow trie) and still does by Jaune things that are slow there
    (decoding, the headers' hashes, the precompiled contracts).
  - What this does not show: anything on the minimal runtime or in the guest; anything about blocks that
    should be refused, or witnesses that are short or wrong (the engine's own refusals are untested);
    Ethereum's test suites. Nothing that serves requests uses the engine yet. The precompiled contracts,
    the decoding of blocks and transactions, the recovery of senders and the receipts root are still
    Jaune's, reached through `Evm/Bridge.lean`. An empty account that is touched is not removed
    (EIP-161).
- **The engine answers requests** (2026-11-21; `evm/Evm/Engine.lean`). A stateless request with `JWIF1`
  for its first five bytes is judged by the engine and answered in the same 69 bytes. A refusal now
  carries the engine's world back, so a block the engine refuses is answered invalid when all it had
  read was proven, and "witness short" when not. `stateless-test` puts both judges through the same
  cases and they agree: 279 blocks of the test chains with whole witnesses, 1,143 witnesses with one
  node, key or code left out (564 answered with no verdict by each), a block lying about its state root
  refused, and on three blocks of mainnet 90 of 90 addresses left out answered with no verdict.
  - **On the minimal runtime, 21 blocks of mainnet as processes: 47.3 seconds through the engine for 64.7
    through Jaune, the same 21 answers.** A third less, not the half and more that Lean's own runtime
    shows (23.3 for 36.1), and `engine-time` says why. Of 44.2 seconds through the engine there, running
    the blocks is 30.3, and with every precompiled contract answering at once that it failed (a rough
    floor, not the same blocks) running them is 1.3: about 29 seconds, two thirds of everything, is
    Jaune's precompiled contracts, which are arithmetic on big numbers that the minimal runtime does
    without GMP. One bn254 pairing takes 582 ms there for 162 on Lean's runtime, a 2048-bit modexp 124
    for 4. The 21 blocks call ecrecover 917 times, bn254 addition 226, multiplication 221, pairing 15
    (48 pairs), modexp 37, the KZG check 8. After that: recovering senders 4.7 seconds, reading the
    witness 2.8, the state root 2.5, the receipts root by Jaune's trie 2.2. So what is next is not the
    engine, which is about 60 ms a block there, but bn254 and the other curves on fixed-width words,
    which the plan had last.
  - Not run: the engine in the guest (the image has not been rebuilt since it could not answer `JWIF1`);
    Ethereum's test suites; the 100 further blocks on the minimal runtime. The builder does not use the
    engine.
- **The engine reads the witness as it goes** (2026-11-21; `Witness` in `evm/Evm/Bridge.lean`). An account
  or slot is looked up in the witness's trie when the engine comes to it, by the hash of what it has in
  hand, and the answer is found, proven absent, or not said, which marks the world and ends in "witness
  short". Nothing is made into a state beforehand, and the addresses and slot numbers in a request are
  not used. All 121 blocks agree with their headers as before. In `stateless-test`, of the 1,143
  witnesses with a piece left out the engine now answers 734 rightly and 409 with no verdict, where
  Jaune's path answers 564 with no verdict; neither ever answers otherwise. It is not faster for it on
  Lean's runtime (each lookup walks down from the root, decoding the same upper nodes again: reading the
  witness and running the block took 236 ms at the median before and take 244 now) and a little faster
  on the minimal one, where the 21 blocks through the service take 25.9 seconds for 27.5. Keeping the
  nodes it has opened would be the next thing here.
- **The builder on the engine** (2026-11-21; `evm/Evm/Build.lean`). A request to build that begins `JBLF1`
  is built by the engine: the same template, the same rule for what goes in and in what order, the same
  response, and the same machine of steps that a clock can cut short. A transaction that asks the witness
  for what it cannot prove is undone whole, payment and nonce with the rest, and left out. `build-test`
  puts every case to both builders and both pass all of it, 425 checks each: three test blocks built
  again as given come out with the chain's hash; built by the rule they are blocks Jaune's checker
  accepts; cut short before the first transaction and half way they are still such blocks; and with each
  node, key and code of the witness left out in turn, under both rules, nothing is built or a block the
  checker accepts is (the engine builds nothing 90 times of 808 where Jaune's builds nothing 110 times).
  Three blocks of mainnet built again from their own transactions come out with the chain's hashes by
  both, and by the rule both put in the same number (97, 104, 101). On Lean's runtime the engine takes
  171 to 279 ms for those where Jaune's builder takes 422 to 749, and 32 ms for the test block of 8M gas
  of delegate calls where Jaune's takes 401. A request for a bid (`JBID2`) carries either kind, so the
  guest will sign a block built either way once an image has both. Not run: the minimal runtime, the
  guest, the shadow builder; blocks of mainnet with addresses left out (`build-test real`) by the engine.
- **bn254 on machine words** (2026-11-21; `evm/Fast/Bn254.lean`): the field in Montgomery form on four
  words, the tower above it, both groups, and the optimal ate pairing, for the three precompiled contracts
  that use the curve. Its constants were worked out from the curve's prime, order and parameter, not
  copied. `bn254-test`: the field against `Nat` on 3,000 pairs, and the three contracts against Jaune's on
  760 additions, 413 multiplications and 42 pairing checks (points at infinity, points not on the curve,
  numbers not under the prime, inputs short and long, gas one short of enough): the same success, gas and
  bytes every time. All 121 blocks still come out as their headers have them. **On the minimal runtime
  the 21 blocks through the service now take 27.5 seconds by the engine for 64.9 by Jaune, 2.4 times, the
  same 21 answers; the median block 1.25 seconds for 2.61.** Running the blocks fell from 30.3 seconds
  to 10.2. What the 26 seconds are now: running the blocks 10.2 (the other precompiled contracts are
  still Jaune's: ecrecover, the KZG check on BLS12-381, modexp), recovering senders 4.7, reading the
  witness 2.8, the state root 2.5, the receipts root by Jaune's trie 2.3. Not tested: a point of the
  twist that is on its curve and not in the pairing's subgroup (making one needs a square root the test
  does not have; the check is there, by multiplying by the order). Nothing is proved, and none of it is
  constant time, which nothing here needs. On the minimal runtime a pairing check of one pair takes 4.5
  ms for Jaune's 574, and a point times a number 0.39 ms.
  - What the precompiled contracts that are still Jaune's cost in those 10.2 seconds, roughly, by
    running the blocks again with one kind failing at once (`engine-time`): the KZG check about 7.4
    seconds for 8 calls, most of a second each; ecrecover 1.3 seconds for 917; the three on bn254, now
    the engine's, 0.9; SHA-256, RIPEMD-160 and identity 0.4; modexp 0.1. With all of them failing the
    21 blocks run in 1.2 seconds. The KZG check is BLS12-381, which is to be done as bn254 was. It
    matters to a checker of blocks; a builder that takes no blob transactions seldom meets it.

What is known to be left in the time: the minimal runtime's allocator (issue #1), the stack held as a
list whose length is counted at every push (3%), extension fields held as lists of big numbers (13%, in
both pairings), keccak in Lean (5%), and a request's 0.9 seconds on its way in.

What it stands on that is not sound yet:

- [ ] **Seven of mathlib's start-up routines are replaced by routines that do nothing** (`evm/rt/start.c`).
      Jaune's modules import mathlib for proofs, which is what this repository's own rule forbids in code
      that runs. Nothing proves that no constant those routines would have built is read; the fixtures
      agreeing is the evidence. The repair is in Jaune: proofs out of the modules that run.
- [ ] **`main` runs on a 64 MiB stack with nothing under it** (`evm/boot/stack.c`). Firmware's stack is too
      small for Jaune's recursion, and how deep a hostile block can make it recurse has not been measured.
- [ ] **The three runtime functions it adds are in `evm/rt/`, not in `rt/`**, and are held to Lean's runtime
      only by `evm-test` (212 cases of `powMod`) and by the fixtures. If the service stays, they go through
      what every other runtime function went through.
- [ ] **Nothing in `evm/` is built or run by CI.**

Not done:

- [ ] A witness that is always enough. `evm/witness/fetch` now adds what the service says it lacks and
      tries again, which was enough for 121 blocks of 121; it knows how to add an address or a slot number,
      not a trie node, and a node that keeps no proofs of past state (reth's default) could not supply one.
- [ ] A verdict on a block that is rejected while it runs. That is answered with status 8, which is no
      verdict, because Jaune's error does not carry what had been read up to then.
- [ ] Proofs that the three things the branch of Jaune runs in place of its definitions are equal to them:
      the jump-destination check, sender recovery over fixed-width words, and the bn254 final
      exponentiation. They are tested (above, and `THREAT_MODEL.md`), which was decided to be enough for
      now.
- [ ] Time, beyond the line. A median of 3.0 seconds a block in the guest on one run (above), with the
      slowest block in a hundred at 19.
- [ ] A request on its way in faster than 8.5 MB a second. Each segment is acknowledged on its own and
      costs the guest two exits to the host; acknowledging several at once is the next thing to try.
- [ ] A full check of the attested answer. The quote is checked up to Intel's root key in a browser
      (above); TCB status, revocation and the quoting enclave's version are not, the measurements are compared
      only with ones the same operator recorded, and no one has verified a quote off this host with DCAP.
- [ ] The measurements derived from the image and the firmware, so that a quote can be tied to a commit
      without a TDX machine to boot it on.
- [ ] Any fork but Prague has been run. Cancun and Osaka are accepted and untried.
- [ ] More than one request at a time, or anything else while one runs: the machine reads no packet until
      the import returns.

## The OS

Lean all the way down, booting in a Nitro Enclave with no Linux, no libc and no AWS-supplied boot files,
answering its parent over vsock and returning an attestation that verifies off-host.

**Done on 2026-11-15.** `silo-os.eif`, as CI built it, ran in a real Nitro Enclave (m5.xlarge, us-east-2,
not in debug mode). From its parent it answered the whole test conversation; its self-test digest was the
one computed on Lean's own runtime; and the attestation document it returned verified on another machine,
against the AWS root, with the nonce that was sent and the measurements CI reproduced from source. The two
documents are kept in `verify/vectors/`, and `boot/README.md` records what a real enclave looked like to
the image.

### Done

- [x] The demo service: framing and commands as pure Lean, with tests (`Demo/`, `demo-test`).
- [x] Measured what compiled Lean needs from a runtime: 108 functions for everything here and for
      the first service built on it (`scripts/measure-runtime`, `rt/live-symbols/`).
- [x] The minimal runtime (`rt/`): same output as Lean's own runtime for the self-test, the big-number test
      and the demo service, as a process on Linux and macOS, and under AddressSanitizer and UBSan. In a real
      enclave the self-test digest matched.
- [x] The boot stub (`boot/`), entered three ways. A real enclave uses the Linux boot protocol's 64-bit
      entry with the image at 1 MiB, which then moves itself to where it runs. The 32-bit entry and the PVH
      entry have only been used by QEMU. No loader has put the image anywhere but 1 MiB, so a test shape
      does: it moves itself to 48 MiB before entering, and the image finds its way home and runs the
      self-test; moved on top of where it has to go, it says so and stops.
- [x] The kernel image (`<name>.bzImage`, made by `mkimage`) and the enclave image file packed from it with
      AWS's open-source builder (`scripts/build-eif`). CI builds both twice from nothing and they agree byte
      for byte; a real enclave reported the same measurements.
- [x] Lean on bare metal: the self-test and the big-number test print over serial what they print as
      processes. Under QEMU only (a real enclave ran the self-test, not the big-number test).
- [x] The device layer in Lean: checked access to registers and device memory, virtio over memory-mapped
      registers, polled queues.
- [x] The vsock protocol in Lean, with scenarios and a fuzzer, and the socket device driver. In a real
      enclave, and under QEMU against Linux's vhost-vsock and against vhost-device-vsock.
- [x] The boot heartbeat (connect to the parent, send `0xb7`, expect it back), when the command line asks
      for it with `silo.heartbeat=CID:PORT`. `nitro-cli` accepted it from a real enclave.
- [x] The Nitro Secure Module: its messages (`Kernel/Nsm.lean`) and its driver
      (`Kernel/SecureModule.lean`). `attest` and `random` are served from the device, and random bytes
      come from it and not from the processor's generator. In a real enclave, and against the module QEMU
      emulates.
- [x] The demo service as a whole machine (`silo-os`), answering the test conversation (`sim-test`) and the
      parent's client (`ask`) from a real enclave's parent, through socat.
- [x] The off-host attestation verifier (`verify/verify-attestation`, Python: COSE signature, certificate
      chain to the AWS root, the document's shape, measurements, nonce). Tested against documents forged
      under a made-up authority and against two a real enclave returned, one of them from debug mode, which
      it refuses. It holds the chain to revocation lists it is given (`--crl`), tested on made-up lists and on
      the one AWS publishes for the first authority under its root.
- [x] The probe (`virtio-probe`): what a machine looks like from inside. Its report from a real enclave is in
      `boot/README.md`.
- [x] Memory with only the rights it needs: code not writable, data not runnable, nothing else mapped, a hole
      under the stack, exceptions on their own stack (`scripts/check-protection`). The image and device
      registers are mapped in 4 KiB pages and the registers uncached; the heap in 2 MiB pages. The checks
      themselves are run under QEMU only: they stop the machine on purpose. An image mapped this way has
      run in a real enclave (`boot/README.md`).
- [x] A rehearsal under QEMU's emulation of a Nitro Enclave, in every CI run: QEMU unpacks the EIF and boots
      it, the heartbeat goes to the parent at address 3, the service answers its test conversation, and the
      attestation document carries the measurements AWS's builder wrote down.
- [x] The socket driver and the Secure Module's against a device that lies (`driver-test`,
      `rt/hosted/machine.c`): on a machine made of ordinary memory, with the real device layer, the test
      writes what it likes into the queues and the drivers are never led outside what they were given. A device that takes nothing the driver sends leaves
      the socket stuck, and the machine stops.
- [x] The memory mapping's checks and the big-number test in a real enclave, on 2026-11-16 (an m6i.xlarge,
      debug mode, `scripts/enclave-checks`): each of the ten forbidden things was refused there as under
      QEMU, the page beside the device registers included, and the big-number test printed the 71 lines
      Lean's own runtime prints. The images are the probe, which answers the boot heartbeat first; an
      image that does not is shown nothing of.
- [x] Timing that does not depend on data: the boot stub turns the processor's mode on where it is offered.
      In a real enclave on an m6i.xlarge (Xeon Platinum 8375C) on 2026-11-16 it was offered and turned on;
      under QEMU, and on the m5 used before, it is not offered.
- [x] Proved about the vsock protocol (`Kernel/VsockProofs.lean`): no packet and no sequence of packets and
      calls makes the table of connections hold more than the endpoint allows, and a write takes no more
      than the peer has said it has room for. Not proved: that the packets a write emits carry exactly the
      bytes it says it took, and the counters once they wrap; the scenarios and the fuzzer cover those.
- [x] AWS's image builder is built in CI from source at a fixed commit, with every dependency's version fixed
      by a lock file kept here (`third_party/eif_build/`) and a fixed compiler.
- [x] Lean images build on any host, given an unpacked x86-64 Linux Lean release (`scripts/build-bare`). The
      measurements that count are those of the image built on x86-64 Linux, as CI does.

### Proofs about the runtime's Lean

`Runtime/BigProofs.lean`, checked by the build, on Lean's three standard axioms. `Runtime/Utf8Proofs.lean`,
checked by the build too, but its questions about bytes are settled by `bv_decide`: a SAT solver's answer
checked by compiled code, so those theorems also trust the compiler that ran the check.

- [x] What number a row of limbs is, and that `trim` leaves it as it was.
- [x] `add` returns the limbs of the sum; `sub` of the difference where there is one; subtraction of
      natural numbers stops at zero.
- [x] `mul` returns the limbs of the product.
- [x] `compare` says which of two numbers is larger.
- [x] One more decimal digit is times ten plus the digit.
- [x] Signed multiplication.
- [x] Signed addition and comparison, on numbers with no zero limb on top. Comparison also assumes that a
      number passed as below zero is not zero: `intCompare` would call "minus zero" less than zero.
      `Mini/Number.lean` is shown never to pass one for an integer that arrives as a tagged word (the sign
      it passes is 1 only for a number below zero), nor for one that arrives as an object of the kind this
      program makes, whose top limb is not zero. That `checked` stops on any other object is not proved.
- [x] Shifts left and right by any count a machine word holds (times and divided by that power of two,
      rounding down), `and`, `or`, and powers for any exponent a machine word holds.
- [x] Division: the quotient rounded down and the remainder, for any dividend and any divisor that is not
      zero and has no zero limb on top. By a single limb, and by two limbs or more, which is Knuth's
      algorithm D. Proved of that one: the shift sets the divisor's top bit; each guess at a quotient limb
      is never too small and at most one too large, and `refine` gets there in at most twice round, so its
      count of four is never used up; taking the guess off says rightly whether it went below zero; and
      putting the divisor back once then leaves the right remainder, the carry out of the top cancelling
      the borrow. On top of it `natDiv` (by zero gives zero), `natMod`, `intEdiv` and `intEmod` are what
      Lean's `Nat` and `Int` define. A quotient or remainder can come back with zero limbs on top, and a
      zero quotient with a minus sign; `Mini/Number.lean` takes the limbs off and makes any zero plain
      zero, which is proved (the item after the next).
- [x] `Runtime/Utf8.lean` against the standard's table (RFC 3629), stated in plain arithmetic
      (`Runtime/Utf8Proofs.lean`). `write` gives the table's bytes for every character up to U+10FFFF.
      `strict` says one, two, three or four exactly when that many bytes are there and they are the encoding
      of a character Unicode allows, so never for a surrogate, an overlong form or anything above U+10FFFF.
      Where `strict` finds a character, `read` returns the one those bytes encode and `claims` steps over
      exactly its bytes. Not stated: what `read` and `claims` answer on bytes that are not well formed, where
      they follow Lean's own runtime, which is C and has no definition here to be held against.
- [ ] That `Mini/Number.lean` hands the arithmetic the right limbs and reads its answer rightly. Proved at
      both ends of a call to the arithmetic, for numbers of every size, and for nine operations on natural
      numbers as wholes (`Mini/NumberProofs.lean`, on Lean's three standard axioms), about the program as
      its language defines it. Not proved: what the wholes assume, and the other operations as wholes (the
      last paragraphs here).

      A number that fits in a tagged word:
      - Going in, a natural number: `limbs_of_word`, and `nat_limbs` for one that arrives as a tagged
        word, leave in memory an array holding the limbs of that number, with no zero limb on top. They do
        nothing C leaves open and change nothing outside the room the allocator gave. All that is assumed
        of the allocator is that it returns an address.
      - Going in, an integer from -2^31 to 2^31 - 1, which arrives as a tagged word holding its 32 bits:
        `int_sign` gives 1 if it is below zero and 0 if not, and `int_limbs` leaves an array holding the
        limbs of the integer without its sign, -2^31 included, on the same terms as above.
      - `trimmed`, for any array of limbs: its loop reads only those limbs, changes nothing, and gives the
        count without the zero limbs on top.
      - Coming out, a natural number: `nat_result` and `nat_from`, where the number in the array is below
        2^63, give back the tagged word for it (twice the number, and one), whatever zero limbs the
        arithmetic left on top.
      - Coming out, an integer: `int_result`, and `int_from` on an array as the arithmetic returns one
        (limbs, then a sign), where the integer is from -2^31 to 2^31 - 1, give back the tagged word
        holding its 32 bits, whatever zero limbs were left on top. A zero with a minus sign comes back as
        plain zero. The integer `int_from` is proved to read is `signedValue`, the one
        `Runtime/BigProofs.lean` proves the arithmetic's answers about.

      A number that is an object (a header, a sign, a count and that many limbs of four bytes):
      - Going in: `checked` passes an object whose top limb is not zero and whose sign is 0 or 1, gives its
        count and changes nothing. `limbs_of_object` leaves an array holding the object's limbs. On those,
        `nat_limbs` does so for a natural number of 2^63 or more, `int_limbs` for an integer outside
        -2^31 to 2^31 - 1, and `int_sign` gives the sign the object holds.
      - Coming out: `big_new` leaves an object holding a sign and the first limbs of an array. On it,
        `nat_result` and `nat_from` for a number of 2^63 or more, and `int_result` and `int_from` for an
        integer outside -2^31 to 2^31 - 1, give back an object holding the array's limbs without the zero
        ones on top, so the same number, with a top limb that is not zero. What goes out is therefore what
        the theorems about going in assume of what comes in.
      - What these assume of the allocator, as hypotheses in each statement: the room it hands out shares
        no byte with the object or array being read, and handing it out left that object or array as it
        was. Nothing is assumed of what the room held. Also assumed: that an object's address has its
        lowest bit clear, which is how the program tells it from a tagged word, and that an array has
        fewer than 2^32 limbs. Where an array is given up at the end (`nat_from`,
        `int_from`), the object is shown right in the state `lean_dec` is handed, and is what the function
        gives back if `lean_dec` returns; what `lean_dec` then does to memory is the allocator's and is
        not stated here.
      - Not proved of `checked`: that it stops on an object that is not well formed. The theorems say what
        happens for an object that is.

      An operation as a whole, from the words compiled Lean hands in to the word it gets back:
      - `lean_nat_big_add`, `_sub`, `_mul`, `_div`, `_land` and `_lor`. Handed two natural numbers as
        compiled Lean holds them (a tagged word below 2^63, an object of its own from there up), if the
        operation returns, it returns the sum (the difference stopping at zero, the product, the quotient
        with division by zero giving zero, the and, the or) as compiled Lean holds it, and every object
        that was there before is there and as it was.
      - `lean_nat_big_eq`, `_le` and `_lt`, on the same terms, return 1 where the numbers are equal (the
        first at most the second, the first below the second) and otherwise 0.
      - They hold for any amount of fuel: a run that finished finishes the same with more.
      - They are statements of an operation that returns. Where `lean_alloc_object` does not return, each
        function on the way is shown not to return either, so none carries on with an address it was not
        given.
      - What they assume, each a hypothesis in the statement. Of the allocator (`Allocator`): room it
        hands out is at an even address, was no object's, and is the new object's; handing it out, and
        giving up an array of limbs, leave every other object there and as it was; and writing inside
        objects that were handed out does not disturb it. Of the compiled arithmetic (`Computes`,
        `Compares`): handed two different arrays of limbs, each an object of its own, it returns an array,
        an object of its own, holding what the function in `Runtime/Big.lean` gives for those limbs (for a
        comparison, that function's answer), and leaves every object but the two there and as it was. And
        that the arithmetic's answer has fewer than 2^32 limbs.

      Not proved:
      - The assumptions. Nothing shows that `Mini/Alloc.lean`, with the reference counting above it,
        meets `Allocator`; no allocator is shown to. `Computes` and `Compares` are what the Lean compiler
        and Lean's own array code are trusted for.
      - The other operations as wholes: `lean_nat_big_mod`, the shifts, the power and the logarithm, the
        conversions to and from machine words, `lean_cstr_to_nat`, and every operation on integers.
      - An answer of 2^32 limbs or more, where `big_new` reports that memory has run out.

### The code under Lean, written in Lean

`Mini/` is a language of 64-bit words, small enough to define exactly (`Mini/Run.lean`), from which C is
printed. What is reasoned about and what is compiled are then the same text.

- [x] The language, its meaning as an interpreter that fails wherever C leaves the outcome open, and its
      printer.
- [x] The allocator in it. Its C is printed when the runtime is built, and the runtime's tests pass on it as a process, under
      the sanitizers and on bare metal. Run as the language defines it, it never reads memory nothing has
      written or steps outside an array, over a test of 300 requests and frees.
- [x] First proofs about the allocator, for every input (`Mini/AllocProofs.lean`): what `class_bytes` gives
      for a small class, and that a request of 1 to 4096 bytes is given a class whose block holds it with
      fewer than sixteen bytes to spare.
- [x] `rt_malloc` itself, on one path, for every state and size that meet its conditions (`malloc_fresh`): a
      request of 1 to 4096 bytes, with no freed block of its class waiting and room on the heap, does
      nothing C leaves open, returns the front of the heap past a sixteen-byte header holding its class
      and "in use", and changes nothing else.
- [x] Memory (`Mini/Memory.lean`): reading back a word just written gives the word, and a write leaves
      every read of other bytes as it was.
- [x] `rt_malloc`'s other path for a small request (`malloc_reuse`): with a freed block of its class waiting,
      whose first word is its link and whose header says it is free, it hands out that block, takes it off
      its list, clears the link, marks it in use, and changes nothing else.
- [x] `rt_free` for a block of a small class that is in use (`free_small`), for every such state: it marks
      the block free, writes zero over every byte it held (the loop, for any size: `zero_loop`), links it in
      front of its class's list, and changes nothing else.
- [x] The first of the invariant (`Mini/AllocHeap.lean`): a heap is in order when the blocks handed out so far
      lie one after another from where it began, each behind a header that says its class and state. A small
      request served from fresh heap keeps it in order with the new block added (`malloc_fresh_in_order`):
      so such a block shares no byte with any handed out before, and every earlier header is untouched.
- [x] The heap stays in order through freeing and reuse too. Writing inside a block's own bytes, marking a
      block in use or free, and zeroing it leave every header as it was (`Laid.frame_body`, `Laid.mark`,
      `Laid.zeros`); so freeing a block that was handed out (`free_small_in_order`, about the program
      itself) and handing one out again (`reuse_keeps`) keep the same blocks laid as they were.
- [x] The allocator on small blocks, for any sequence of calls (`Mini/AllocHeap.lean`). A heap is sound when
      the blocks handed out so far lie one after another, each behind a header that says its class and
      state, and every class's list is a chain of freed blocks of that class, none on it twice. Proved:
      - no two blocks that were handed out share a byte, headers included (`Laid.separate`);
      - whatever is written inside a block's own bytes, every header stays as it was (`Laid.frame_body`);
      - a heap from which nothing has been handed out is sound (`empty_sound`);
      - `rt_malloc` for 1 to 4096 bytes, from a waiting freed block or from fresh heap, and `rt_free` of a
        block that was handed out and is in use, each do nothing C leaves open and leave a sound heap sound
        (`malloc_reuse_sound`, `malloc_fresh_sound`, `free_small_sound`). These are about the program
        itself, and one call's result meets the next call's conditions.
- [ ] Still outside those theorems: blocks over 4096 bytes (the loop that finds a power of two, and their
      lists), the first call (which asks the platform for the heap), and running out of room, which stops
      the machine through a call out of the program. That a freed block is all zero is shown for the
      moment it is freed (`free_small`); it is not yet part of what "sound" says, so it is not shown to
      still hold later.
- [ ] What the caller has to keep to, and nothing here checks: that it frees only what it was handed, once.
      Freeing a block twice is caught by the header and stops the machine; freeing an address that was
      never a block is not.
- [ ] That the printer and the C compiler keep the meaning. Trusted, and now tested for the allocator:
      `scripts/fuzz-alloc` puts made-up requests (every size, frees, words written and read back, a block
      freed twice, running out) to the program as its language defines it and to the printed C compiled
      under the sanitizers, and they have to agree on every answer. Three faults put into the C on purpose
      were each caught within a few rounds. CI runs a short one. The other programs have nothing like it
      yet: freeing, numbers and arrays need objects made up for them, which is the next harness.
- [x] Giving up references and freeing (`Mini/Free.lean`): the same checks as the allocator's
      printed C. Not yet run as the language defines it, and nothing proved.
- [x] What a number too large for a word is in memory (`Mini/Number.lean`), in place of `rt/big.c`.
- [x] Arrays and byte arrays (`Mini/Array.lean`), in place of `rt/array.c`.
- [x] The small cases of shifts, powers and logarithms (`Mini/Small.lean`) and Lean's byte hash
      (`Mini/Hash.lean`), in place of `rt/nat.c` and `rt/hash.c`. The hash, run as the language defines it,
      gives what Lean's own gives.
- [x] Strings (`Mini/String.lean`), in place of `rt/string.c`. Run as the language defines it against Lean's
      own strings (`mini-test`): every operation, every byte position on and off a character, shared and
      unshared, with and without room. Any read of a byte not written, write past an object or into a
      freed one, or overlapping copy fails the run; faults put in on purpose (an off-by-one in the room
      check, a missing clamp, an over-read, a copy one byte long) were each caught. Not yet proved.
- [ ] Strings proved in bounds: every read and write inside the objects it was given or made.
- [ ] The rest of `rt/`, a file at a time: making objects permanent, start-up, stopping.
- [ ] Say where each piece of hand-written C and assembly comes from in other systems, and where it parts
      from them: the boot header and page tables (Linux's boot protocol and `head_64.S`, seL4's boot code),
      polling instead of interrupts (Solo5, DPDK), size classes (Linux's SLUB, seL4 has no kernel heap at
      all), closures (`caml_applyN` in OCaml), one address space at full privilege (MirageOS, Unikraft).
      References by file and function, never copied code.
- [x] The real mapping (`Mini/Map.lean`), in place of the page-table code in `boot/early.c`, which keeps
      only the reload of the root. `mini-test` asks it about every 2 MiB stretch of the first four
      gigabytes and every 4 KiB page of those mapped small: none is both writable and runnable, each maps to
      itself, and the code, constants, data, the stack's hole, heap and registers each get what they should.
      Faults put in on purpose (data runnable, the hole mapped, registers cached) were each caught. The whole
      `boot_map` is run only under QEMU (`scripts/check-protection`): the interpreter keeps memory as a
      chain of single-byte writes, and 3,500 words of page tables make that take minutes.
- [ ] Prove the mapping: every entry `boot_map` writes is inside the directories or the tables it was
      given, and no entry is both writable and runnable.
- [ ] Memory in the interpreter that does not slow down with every write, without changing what it means.
- [ ] A back end for the small language that writes x86-64 machine code itself, no C compiler, starting with
      the boot path (a stage0 / Forth-style bootstrap: a tiny, checkable translator instead of clang for the
      code that runs before memory protection is on). Then the translator, being small, can be checked
      against the interpreter instruction by instruction, and in time proved.
      Calling a function through its address, and floating-point bits, need the language to grow first.

### What the program's text does not say: speculation and bits that flip

The proofs are about what the program computes. They say nothing about what a processor does ahead of
knowing, or about memory that changes without being written. The parent shares the machine's cache with
the enclave, chooses every byte it parses, and may own the memory rows beside its own. One program running
one thing at a time removes the attacks that need the attacker's code inside, or something to interrupt;
it does not remove these. Four things to do about them:

- [ ] Build what we compile with the compiler's hardening against speculation: speculative-load hardening
      (a bounds check guessed wrong cannot feed a read out of bounds), retpolines, and hardening of
      straight-line speculation. The compiler Lean ships takes all of them for this target. That covers the
      C here, the C printed from `Mini/`, and the Lean modules compiled for an image. Measure what it costs
      in time and size. Lean's own `Init` and `Std` come compiled without it, about half an image; hardening
      them means building Lean's library ourselves, which is a step of its own.
- [ ] Catch corruption where it cannot be prevented. The allocator's headers hold values that are checked on
      every free and reuse. Offer the same to services: a cell that keeps a value in two forms and stops the
      machine if they disagree when it is read, for a key, a counter or a limit.
- [x] Tricks from C libraries, in the small language and proved or checked: an index past a bounds check
      masked without a branch (Linux's `array_index_nospec`, `Stmt.inBounds`, in strings and in `hw.c`);
      a compare and a select whose time no secret decides (libsodium, BearSSL: `Mini/Secret.lean`, used
      from Lean as `Secret.equal` and `Secret.select`), with a check of any function's text for the same
      (`Mini/Constant.lean`); the allocator's wipe kept from the compiler (OpenBSD's `explicit_bzero`,
      `Stmt.keep`); eight ASCII bytes at a time (glibc, musl, simdjson), reading only what belongs to the
      string; and sums and products of sizes checked in the language instead of assumed of Lean's header
      (`Mini/Checked.lean`). The arithmetic in each is proved in `Mini/WordProofs.lean`.
- [ ] Keep secrets out of reach of a guess: not beside input that is being parsed, and wiped the moment they
      are finished with. Say how in `CONTRIBUTING.md`, and make the runtime help where it can.
- [ ] Say all of this in `THREAT_MODEL.md`, which today says only that speculation is left to AWS: what the
      design removes, what the build hardens, what is caught, and what stays AWS's (the memory itself, and
      what one guest can do to another's).

### Hardening the OS, before anything secret runs on it

Nothing is open here.
