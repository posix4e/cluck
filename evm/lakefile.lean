import Lake
open Lake DSL

/-! An Ethereum block importer as a service on silo-os: Jaune's executable specification of the EVM, taking
a request of bytes and answering with bytes. An experiment, kept in a package of its own so that nothing in
it is part of the OS or of an image the OS releases (README.md here, and THREAT_MODEL.md above). -/

package «evm»

require «silo-os» from ".."

/-- Jaune, at the commit this was built and run against. Its own manifest pins mathlib. -/
require jaune from git "https://github.com/posix4e/jaune" @ "3c2835998fe13be9bb6e9ddd21bbdc4a71db6670"

/-- The service: requests, responses, and the block import between them. Pure. -/
@[default_target]
lean_lib Evm

/-- An execution engine written for speed, to take Jaune's place in what runs. Imports no proofs. -/
@[default_target]
lean_lib Fast

/-- What the guest needs to keep a secret on a wire: hashes, a cipher, a key exchange, and in time a TLS
client. Written here because nobody else's may go in an image. Imports no proofs and no Jaune. -/
@[default_target]
lean_lib Tls

/-- The platform as an ordinary process, from the OS's own source. -/
target platformHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / ".." / "rt" / "hosted" / "platform.c")
  buildO (pkg.buildDir / "rt" / "platform_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- The EFI services as an ordinary process finds them: absent. -/
target efiHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / ".." / "rt" / "hosted" / "efi.c")
  buildO (pkg.buildDir / "rt" / "efi_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- A clock for the benchmark, which only ever runs as a process. -/
target clockHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "clock.c")
  buildO (pkg.buildDir / "rt" / "clock_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- The OS's two functions for secrets (`Secret.lean` above, over `Mini/Secret.lean`) printed as C and
compiled, for what runs on Lean's own runtime. The minimal runtime prints them with the rest. -/
target secretHosted pkg : System.FilePath := do
  let some printer ← findLeanExe? `«mini-print» | error "no mini-print"
  let printed ← (← printer.fetch).mapM fun exe => do
    let c := pkg.buildDir / "printed" / "secret.c"
    IO.FS.createDirAll (pkg.buildDir / "printed")
    IO.FS.writeFile c (← captureProc { cmd := exe.toString, args := #["secret"] })
    return c
  buildO (pkg.buildDir / "printed" / "secret.o") printed
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- The service as a process: one request on standard input, one response on standard output. -/
@[default_target]
lean_exe «evm-serve» where
  root := `ServeMain
  moreLinkObjs := #[platformHosted, secretHosted]

/-- The service as a whole machine: an EFI guest answering framed requests over TCP. -/
@[default_target]
lean_exe «evm-os» where
  root := `EfiMain
  moreLinkObjs := #[platformHosted, efiHosted, secretHosted]

/-- The same machine with the stand-in relay for its only relay, for trying things on one machine. -/
@[default_target]
lean_exe «evm-os-shadow» where
  root := `EfiShadow
  moreLinkObjs := #[platformHosted, efiHosted, secretHosted]

/-- Turns one case of a blockchain-test fixture into a request and the response the fixture calls for.
Runs on Lean's own runtime only: it reads JSON. -/
@[default_target]
lean_exe mkrequest where
  root := `MkRequest

/-- Pure tests of the request format and of the one piece of arithmetic this package adds. -/
@[default_target]
lean_exe «evm-test» where
  root := `EvmTest

/-- The fast engine's word arithmetic against `Nat`. Its output is the same on both runtimes. -/
@[default_target]
lean_exe «fast-word-test» where
  root := `FastWordTest
  moreLinkObjs := #[platformHosted]

/-- The fast engine's interpreter against Jaune's, a program at a time. -/
@[default_target]
lean_exe «fast-op-test» where
  root := `FastOpTest

/-- Saved blocks of the real chain through the fast engine, each block's header the judge. -/
@[default_target]
lean_exe «fast-replay» where
  root := `FastReplay

/-- Where the time goes when the fast engine checks a block, part by part, on either runtime. -/
@[default_target]
lean_exe «engine-time» where
  root := `EngineTime
  moreLinkObjs := #[platformHosted, clockHosted]

/-- The engine's bn254 against `Nat` and against Jaune's three precompiled contracts. -/
@[default_target]
lean_exe «bn254-test» where
  root := `Bn254Test

/-- Ethereum's own tests of chains, put to the fast engine, the fixture the judge. -/
@[default_target]
lean_exe «fast-fixtures» where
  root := `FastFixtures

/-- `Tls/` against the standards' examples and against OpenSSL (`Tls/vectors.txt`). -/
@[default_target]
lean_exe «tls-test» where
  root := `TlsTest
  moreLinkObjs := #[platformHosted, secretHosted]

/-- `Evm/Follow.lean` on consecutive saved blocks of the real chain: proofs carried from block to block. -/
@[default_target]
lean_exe «follow-test» where
  root := `FollowTest
  moreLinkObjs := #[secretHosted]

/-- Blocks put to `Evm/Follow.lean` in one process, to measure the memory following takes (`scripts/follow-memory`). -/
@[default_target]
lean_exe «follow-run» where
  root := `FollowRun
  moreLinkObjs := #[platformHosted, secretHosted]

/-- Drives the TLS client over a real connection, against other people's servers (`scripts/tls-get`). -/
@[default_target]
lean_exe «tls-fetch» where
  root := `TlsFetch
  moreLinkObjs := #[secretHosted]

/-- Times the hashing, the curves and the interpreter, on whichever runtime it is linked against. -/
@[default_target]
lean_exe «evm-bench» where
  root := `Bench
  moreLinkObjs := #[platformHosted, clockHosted]

/-- `Evm.Trie` against Jaune's root computation, through witnesses whole and incomplete. -/
@[default_target]
lean_exe «trie-test» where
  root := `TrieTest

/-- `Evm.Stateless` against the import that has the whole state, with whole and shortened witnesses. -/
@[default_target]
lean_exe «stateless-test» where
  root := `StatelessTest

/-- `Evm.Build` against `Evm.Stateless` and against blocks that exist. -/
@[default_target]
lean_exe «build-test» where
  root := `BuildTest

/-- The signing key's arithmetic against `Nat`, and its signatures against `JauneConsensus`'s. -/
@[default_target]
lean_exe «bls-test» where
  root := `BlsTest
  moreLinkObjs := #[secretHosted]

/-- What became of each transaction in a request to build. For making requests. -/
@[default_target]
lean_exe «build-why» where
  root := `BuildWhy

/-- Checks a signed bid from outside, with the reference's verification. For the host. -/
@[default_target]
lean_exe «bid-verify» where
  root := `BidVerify
  moreLinkObjs := #[secretHosted]

/-- A stateless request's answer in words, with Jaune's reason for a rejection. For making witnesses. -/
@[default_target]
lean_exe «stateless-why» where
  root := `StatelessWhy
