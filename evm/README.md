# evm

An Ethereum block importer as a service on silo-os. A request holds a chain's starting accounts, its genesis
block and some blocks; the service decodes, validates and executes each block and answers with the chain's
tip hash and state root. The execution is [Jaune](https://github.com/skbaek/jaune), an executable
specification of the EVM written in Lean with no foreign code, at the same Lean version as the OS. Nothing
here is a client: there is no network of peers, no mempool and no store, and the whole state travels in the
request.

It is an experiment, in a package of its own. The OS does not depend on it, no image the OS releases holds
it, and continuous integration does not build it. What has been run and what it showed is in
[../TODO.md](../TODO.md); what it adds to the threat model is in [../THREAT_MODEL.md](../THREAT_MODEL.md).

## Layout

- `Evm/Service.lean`: the request and the response, and the import between them. The format is at the top of
  the file. Pure: bytes in, bytes out.
- `Evm/Attest.lean`: a request with a challenge in front, and the REPORTDATA that ties its response to it.
- `Evm/PowMod.lean`: `Nat.powMod` in Lean, which the minimal runtime lacks.
- `ServeMain.lean`: the service as a process, one request on standard input.
- `EfiMain.lean`: the service as a whole machine, an EFI guest answering framed requests on TCP port 5005
  over the OS's own Ethernet, IP and TCP.
- `MkRequest.lean`: turns a case of a blockchain-test fixture into a request and the response the fixture
  calls for. The only program here that reads JSON, and it never goes in an image.
- `EvmTest.lean`: pure tests of the format and of `Evm.powMod`.
- `Bench.lean`: times hashing, curve arithmetic and the interpreter on either runtime.
- `rt/start.c`: seven of mathlib's start-up routines as routines that do nothing, and why.
  `rt/names.c`: three names compiled Jaune asks a runtime for. `rt/hosted/clock.c`: a clock for the benchmark.
- `boot/stack.c`: a 64 MiB stack for `main`, because firmware's is too small for Jaune.
- `scripts/build-min`, `scripts/build-efi`: the OS's scripts of the same names, with what Jaune makes
  necessary. `scripts/run-fixtures`: boots the guest, sends the requests, checks the answers.
  `scripts/fetch-fixtures`: makes `fixtures/` again from its source and compares.
- `demo/`: a web page in front of a guest in a trust domain. `server.py` runs on the host, `page.html` is
  the page, `verify.js` checks a TDX quote in the browser, and `test-verify.mjs` tests that under Node.
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
```

The service as a process, on Lean's own runtime and then on the minimal one. Each answer has to be the
fixture's, byte for byte:

```
scripts/build-min evm-serve
for request in fixtures/*.req; do
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
```

A visitor picks a fixture and whether to send it as it is, with a wrong state root in its last block, or
with a wrong balance in its starting state. The page chooses the 32 bytes, and checks the quote that comes
back itself: Intel's signatures from the quote to Intel's SGX root key, and that REPORTDATA is the hash of
what it sent and of the answer it shows. What that check leaves out is in
[../THREAT_MODEL.md](../THREAT_MODEL.md). The server is on the host and is not trusted by the page; it sends
the guest only the fixtures, never a visitor's bytes. Putting it on a network is the operator's decision
and is done in front of it, with a reverse proxy that speaks HTTPS, which the browser's cryptography
requires anywhere but on loopback.

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
