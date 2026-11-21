# evm

An Ethereum block importer as a service on silo-os. It takes two kinds of request. One holds a chain's
starting accounts, its genesis block and some blocks; the service decodes, validates and executes each
block and answers with the chain's tip hash and state root. The other holds one block, the headers before
it and a witness for the part of the state it touches, which is how a block of the real chain can be asked
about. The execution is [Jaune](https://github.com/skbaek/jaune), an executable specification of the EVM
written in Lean with no foreign code, at the same Lean version as the OS; this package uses a branch of it,
[`posix4e/jaune`](https://github.com/posix4e/jaune/tree/cluck), with four changes described below. Nothing
here is a client: there is no network of peers, no mempool and no store, and whatever state a request needs
travels in it.

It is an experiment, in a package of its own. The OS does not depend on it, no image the OS releases holds
it, and continuous integration does not build it. What has been run and what it showed is in
[../TODO.md](../TODO.md); what it adds to the threat model is in [../THREAT_MODEL.md](../THREAT_MODEL.md).

## Layout

- `Evm/Service.lean`: the request and the response, and the import between them. The format is at the top of
  the file. Pure: bytes in, bytes out.
- `Evm/Stateless.lean`: one block against a witness. The format and every status are at the top of the
  file, with what an answer of "valid" does and does not mean.
- `Evm/Attest.lean`: a request with a challenge in front, and the REPORTDATA that ties its response to it.
- `Evm/Trie.lean`: a Merkle-Patricia trie known only in part, from a witness of nodes named by hash: reads
  that say when the witness falls short, and writes and removals that give the new root.
- `Evm/PowMod.lean`: `Nat.powMod` in Lean, which the minimal runtime lacks.
- `ServeMain.lean`: the service as a process, one request on standard input.
- `Evm/Build.lean`: the makings of a block and a witness, and out of them a block: which of the proposed
  transactions go in, in what order, and the header that follows from running them. The format, the rule
  for ordering and what is left out are at the top of the file.
- `Evm/Sign.lean`, `Evm/Sign/`: a BLS key used without ever being a `Nat`. `Field.lean` is the base field on
  fixed-width words with every value-dependent choice made by the OS's `Secret.select`; `Curve.lean` is
  the key times a point by the same steps whatever the key; `Sign.lean` is public keys and signatures over
  those. Not yet reached from the service. `BlsTest.lean` holds it to `Jaune` and `JauneConsensus`.
- `EfiMain.lean`: the service as a whole machine, an EFI guest answering framed requests on TCP port 5005
  over the OS's own Ethernet, IP and TCP.
- `MkRequest.lean`: turns a case of a blockchain-test fixture into a request and the response the fixture
  calls for. The only program here that reads JSON, and it never goes in an image.
- `EvmTest.lean`: pure tests of the format and of `Evm.powMod`. `TrieTest.lean`: the trie against Jaune's
  root computation. `StatelessTest.lean`: a block with a witness against the same block with the whole
  state, and with every piece of the witness left out in turn.
- `BuildTest.lean`: `Evm.Build` against `Evm.Stateless`, which checks what it builds, and against blocks
  that exist, which it has to build again exactly. `witness/to-build`: turns a request to check a block
  into a request to build one from the same transactions.
- `Evm/Bid.lean`: a block built and the builder's signature over what it offers for it, by a key the
  machine draws when it starts. `BidVerify.lean`: checks such a signature from outside.
  `scripts/check-secret-code`: reads the image's machine code for the key's arithmetic.
- `BuildWhy.lean`: what became of each transaction in a request to build, and why one was left out.
  `builder/shadow`: the builder run in shadow on the host, a block built in the guest for every slot from
  pending transactions, signed by the guest and judged by the node's own validator, and sent to relays only with `--live`. Neither
  goes in an image.
- `StatelessWhy.lean`: a stateless request's answer in words, with Jaune's reason for a rejection and what a
  short witness lacks. `witness/fetch`: makes a stateless request for a block from a node that follows the
  chain. Neither goes in an image.
- `Bench.lean`: times hashing, curve arithmetic and the interpreter on either runtime.
- `rt/start.c`: seven of mathlib's start-up routines as routines that do nothing, and why.
  `rt/names.c`: three names compiled Jaune asks a runtime for. `rt/hosted/clock.c`: a clock for the benchmark.
- `boot/stack.c`: a 64 MiB stack for `main`, because firmware's is too small for Jaune.
- `scripts/build-min`, `scripts/build-efi`: the OS's scripts of the same names, with what Jaune makes
  necessary. `scripts/run-fixtures`: boots the guest, sends the requests, checks the answers.
  `scripts/fetch-fixtures`: makes `fixtures/` again from its source and compares.
- `demo/`: a web page in front of a guest in a trust domain. `server.py` runs on the host, `page.html` is
  the page, `verify.js` checks a TDX quote in the browser, and `test-verify.mjs` tests that under Node.
  `built.html`, at `/built`, shows a block the builder built with its quote; `built.js` checks that the
  quote is for that request and reply, and `test-built.mjs` tests that under Node.
- `fixtures/`: five requests and the responses they must get, made from the Prague cases of five
  blockchain tests in `ethereum/tests` (`fixtures/SOURCES`).

## Build and test

Everything is run from this directory. The first build fetches Jaune and mathlib, about 700 MB of Git
clones; fetch mathlib's prebuilt modules before building, or the build compiles them from source, which takes
hours:

```
lake exe cache get Mathlib.Data.Nat.Basic Mathlib.Data.List.Lemmas Mathlib.Data.List.TakeDrop \
  Mathlib.Data.List.TakeWhile Mathlib.Data.UInt Mathlib.Tactic.NormNum Mathlib.Data.List.Chain
lake build
.lake/build/bin/evm-test
.lake/build/bin/trie-test
.lake/build/bin/stateless-test
```

The service as a process, on Lean's own runtime and then on the minimal one. Each answer has to be the
fixture's, byte for byte:

```
scripts/build-min evm-serve
for request in fixtures/*.req fixtures/stateless/*.req; do
  .lake/build/bin/evm-serve     < "$request" | cmp - "${request%.req}.expected"
  .lake/build/bin/evm-serve-min < "$request" | cmp - "${request%.req}.expected"
done
```

`ShanghaiLove` takes about 40 seconds each way; the others take under ten between them.

The benchmark, which prints what each workload computed after how long it took:

```
scripts/build-min evm-bench
.lake/build/bin/evm-bench
.lake/build/bin/evm-bench-min
```

## As a machine

On an emulated processor, anywhere QEMU and OVMF are installed:

```
scripts/build-efi dev
scripts/run-fixtures dev highGasUsage wallet2outOf3txsRevokeAndConfirmAgain
```

In an Intel TDX trust domain, on a host set up as [../TDX.md](../TDX.md) describes, with the firmware built
there:

```
scripts/build-efi tdx
SILO_TDVF=/path/to/OVMF.fd scripts/run-fixtures tdx
```

`run-fixtures` starts the guest with the OS's `scripts/run-efi`, waits for it to say it is serving, sends each
request in a frame (a 4-byte big-endian length, then the request), and compares the frame that comes back
with the expected response. With no names it sends every fixture. The guest prints one line per request on
its serial port: how long the request was, its status, and how long the import took.

To keep a guest running and put requests to it by hand, give the OS's launcher the image under the name it
looks for, start it, and send the same frame to the forwarded port from another terminal:

```
mkdir -p ../.lake/build/efi/dev/evm-os
cp .lake/build/efi/dev/evm-os/BOOTX64.EFI ../.lake/build/efi/dev/evm-os/
(cd .. && scripts/run-efi dev evm-os)
```

```
python3 - fixtures/highGasUsage.req <<'ASK'
import socket, struct, sys
request = open(sys.argv[1], "rb").read()
with socket.create_connection(("127.0.0.1", 5005)) as s:
    s.sendall(struct.pack(">I", len(request)) + request)
    print(s.makefile("rb").read(4 + 69).hex())
ASK
```

## An answer that says where it came from

A frame that begins with `JATT1` and 32 bytes of your choosing, then a request, is answered with the 69
bytes of the response and, in a trust domain, a 1024-byte TDREPORT. Its REPORTDATA is the SHA-256 of your 32
bytes and the request, followed by the SHA-256 of the response (`Evm/Attest.lean`). The host's quote
generation service signs the report into a quote, as [../TDX.md](../TDX.md) describes, and the quote is what
a relying party checks. The development guest answers the same frame with the response alone.

`demo/` is that exchange as a web page. The server boots the TDX image, keeps it running and listens on
loopback port 5172; it needs Python 3 and the host's quote generation service, and nothing else:

```
scripts/build-efi tdx
SILO_TDVF=/path/to/OVMF.fd demo/server.py record     # boots once and writes down the measurements
SILO_TDVF=/path/to/OVMF.fd demo/server.py
node demo/test-verify.mjs                            # from another terminal
node demo/test-built.mjs /data/eth/shadow/attested N # a block builder/shadow kept, checked as /built checks it
```

A visitor picks a fixture and whether to send it as it is, with a wrong state root in its last block, or
with a wrong balance in its starting state. The page chooses the 32 bytes, and checks the quote that comes
back itself: Intel's signatures from the quote to Intel's SGX root key, and that REPORTDATA is the hash of
what it sent and of the answer it shows. What that check leaves out is in
[../THREAT_MODEL.md](../THREAT_MODEL.md). The server is on the host and is not trusted by the page; it sends
the guest only the fixtures, never a visitor's bytes. Putting it on a network is the operator's decision
and is done in front of it, with a reverse proxy that speaks HTTPS, which the browser's cryptography
requires anywhere but on loopback.

## A block of the real chain

`fixtures/stateless/` holds three requests of the second kind, cut from the fixtures by `stateless-test
write`. For a block of mainnet, a node has to supply the witness. With reth following the chain and serving
`debug` and `eth` on loopback:

```
witness/fetch 26456375 block.req block.expected
.lake/build/bin/evm-serve < block.req | cmp - block.expected
.lake/build/bin/stateless-why block.req
```

The node these were run against was reth 2.11.0 with Lighthouse 8.3.3, started from reth's minimal
snapshot (163 GB to fetch, about 270 GB on disk), which keeps the state of the last 10,064 blocks and so
can make a witness for any of them:

```
reth download --minimal -y --chain mainnet --datadir DIR/reth
reth node --minimal --chain mainnet --datadir DIR/reth \
  --authrpc.jwtsecret DIR/jwt.hex --authrpc.addr 127.0.0.1 --authrpc.port 8551 \
  --http --http.addr 127.0.0.1 --http.port 8545 --http.api eth,debug,net,web3
lighthouse bn --network mainnet --datadir DIR/lighthouse \
  --execution-endpoint http://127.0.0.1:8551 --execution-jwt DIR/jwt.hex \
  --checkpoint-sync-url https://mainnet.checkpoint.sigp.io --http --http-address 127.0.0.1
```

The same requests go to the guest from wherever they were written:

```
SILO_TDVF=/path/to/OVMF.fd scripts/run-fixtures tdx --from DIR 26456375
```

A block can be built as well as checked. `fixtures/build/` holds three requests to build, written by
`build-test write`. For a block of mainnet, a request to check it becomes a request to build it again from
its own transactions, and what comes back has to carry the hash the chain has for that block:

```
witness/to-build block.req build.req
.lake/build/bin/evm-serve < build.req | xxd | head -3     # status 00, then the block's hash
.lake/build/bin/build-test DIR                            # every NAME.req in DIR, as given and by the rule
```

To build from what is pending, every slot, with the node judging each block (reth has to serve `txpool`
and `flashbots` beside `eth` and `debug`, and prove state a few blocks back, `--rpc.eth-proof-window 64`;
a consensus node has to answer on its API):

```
SILO_TDVF=/path/to/OVMF.fd builder/shadow --slots 100       # in a guest in a trust domain
builder/shadow --process --slots 100                         # or as a process, after scripts/build-min evm-serve
.lake/build/bin/build-why /data/eth/shadow/unbuilt/N.req     # why a request built nothing
```

`stateless-test real DIR` and `build-test real DIR` take requests for real blocks and leave addresses out
of their witnesses in turn; a wrong answer or a block the checker refuses fails them.

From another machine, `ssh -L 8545:127.0.0.1:8545 HOST` puts that node within reach of `witness/fetch`,
and everything in this section but the guest then runs anywhere Lean does.

`fetch` asks for the block, the 255 headers before it and the node's own witness, adds the code of every
account the witness names, and writes a request that asks for mainnet's fork schedule. It then puts the
request to `stateless-why`, and while the answer is that the witness lacks a named account or slot it adds
that one and tries again, because a node's witness sometimes leaves out the address of an account the block
reads. `stateless-why` says what the answer was and, when the witness fell short, what it lacked. A witness taken while the node
is still catching up does not hang from the parent's state root and gets no verdict.

The service does not trust the witness. What it relies on, and what its answer means, is at the top of
`Evm/Stateless.lean` and in [../THREAT_MODEL.md](../THREAT_MODEL.md).

## The branch of Jaune

Four commits on [`posix4e/jaune`](https://github.com/posix4e/jaune/tree/cluck), on top of `ba15f39`:

- **Reads are recorded under every fork.** Upstream records the accounts and slots a block reads only under
  Amsterdam, where they go in the block. Stateless validation is sound only if every read can be checked
  against the witness, so the branch records them always and keeps the block's total.
- **A failed or pre-Amsterdam transaction hands its reads over too.** They were dropped on the way from
  the top-level frame to the transaction.
- **What is read in preparing a transaction is recorded**: the account it is sent to, the one that account
  delegates to, and the signer of each EIP-7702 authorization.
- **The jump-destination check compiles to one forward pass.** As written it is exponential on real
  contract code; a mainnet block spent ten minutes in it without finishing. The compiled form is not
  proved equal to the definition: `evm-test` compares it with Jaune's proved linear form.

All of Jaune's own targets, proofs included, build with them. Its conformance suites have not been run on
the branch.

## A request of your own

`mkrequest` reads the blockchain-test format, for the forks Cancun, Prague and Osaka:

```
.lake/build/bin/mkrequest fixture.json Prague my.req my.expected
```

It takes the case of the file whose `network` is the one named. The chain id is 1, the fixtures' own
default. A case with more than one chain of blocks is not supported: the service imports its blocks one
after another onto a single chain.

## What Jaune needed from the OS

Jaune is written for proofs and for Lean's own runtime. Three things stood between it and an image:

- **Start-up.** Three of its modules import mathlib, and a compiled module runs the start-up of everything
  it imports. `rt/start.c` replaces seven routines and says what that assumes.
- **Three runtime functions**: `lean_initialize`, `lean_nat_big_succ` and `lean_nat_powmod`
  (`rt/names.c`, `Evm/PowMod.lean`). With the start-up replaced, that is the whole difference between what
  the block import needs and what the minimal runtime has; `scripts/build-min` fails at the link if it grows.
- **Stack.** More than firmware gives an EFI application (`boot/stack.c`).

## Licences

This package is under the repository's licence, the GNU Affero General Public License, version 3. Jaune and
`ethereum/tests`, which the fixtures are made from, are under the MIT licence; mathlib and what it brings are
under Apache 2.0. None of their source is in this repository. An image built here contains compiled Jaune
and a handful of compiled functions from Lean's library and from mathlib's dependencies.
