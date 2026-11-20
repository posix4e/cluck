import Lake
open Lake DSL

/-! An Ethereum block importer as a service on silo-os: Jaune's executable specification of the EVM, taking
a request of bytes and answering with bytes. An experiment, kept in a package of its own so that nothing in
it is part of the OS or of an image the OS releases (README.md here, and THREAT_MODEL.md above). -/

package «evm»

require «silo-os» from ".."

/-- Jaune, at the commit this was built and run against. Its own manifest pins mathlib. -/
require jaune from git "https://github.com/posix4e/jaune" @ "58e29ee6e24177ab3443333bbe37bad872be6268"

/-- The service: requests, responses, and the block import between them. Pure. -/
@[default_target]
lean_lib Evm

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

/-- The service as a process: one request on standard input, one response on standard output. -/
@[default_target]
lean_exe «evm-serve» where
  root := `ServeMain
  moreLinkObjs := #[platformHosted]

/-- The service as a whole machine: an EFI guest answering framed requests over TCP. -/
@[default_target]
lean_exe «evm-os» where
  root := `EfiMain
  moreLinkObjs := #[platformHosted, efiHosted]

/-- Turns one case of a blockchain-test fixture into a request and the response the fixture calls for.
Runs on Lean's own runtime only: it reads JSON. -/
@[default_target]
lean_exe mkrequest where
  root := `MkRequest

/-- Pure tests of the request format and of the one piece of arithmetic this package adds. -/
@[default_target]
lean_exe «evm-test» where
  root := `EvmTest

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

/-- A stateless request's answer in words, with Jaune's reason for a rejection. For making witnesses. -/
@[default_target]
lean_exe «stateless-why» where
  root := `StatelessWhy
