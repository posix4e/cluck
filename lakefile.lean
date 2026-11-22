import Lake
open Lake DSL

/-! silo-os: a Lean unikernel for AWS Nitro Enclaves (see README.md). -/

package «silo-os»

/-- The demo service: pure framing and commands, no I/O. -/
@[default_target]
lean_lib Demo

/-- The parts of the minimal runtime that are written in Lean: arithmetic on numbers too large for a machine
word and the rules of UTF-8 (`Mini/Number.lean` and `Mini/String.lean` are the rest of each). Linked into everything that runs on the minimal runtime. -/
@[default_target]
lean_lib Runtime

/-- What is proved about `Runtime`: that its arithmetic returns the limbs of the numbers it should. -/
@[default_target]
lean_lib Proofs

/-- A small language for the code under Lean, written as data in Lean, and its printer to C. -/
@[default_target]
lean_lib Mini

/-- Prints the C that the programs in `Mini/` stand for. Runs where the runtime is built, not in it. -/
@[default_target]
lean_exe «mini-print» where
  root := `MiniPrint

/-- The string program run as its language defines it, against Lean's own strings. -/
lean_lib MiniStringTest

/-- The real mapping run as its language defines it, and every entry it writes checked. -/
lean_lib MiniMapTest

/-- The allocator, the byte hash and strings run as the language defines them, with no C involved. -/
@[default_target]
lean_exe «mini-test» where
  root := `MiniTest

/-- Sets the allocator as its language defines it against the allocator as printed and compiled
(`scripts/fuzz-alloc`). -/
@[default_target]
lean_exe «mini-fuzz» where
  root := `MiniFuzz

/-- What the service asks of the platform underneath it: three functions, implemented in C per platform. -/
@[default_target]
lean_lib Platform

/-- The platform as an ordinary process (a pipe and the operating system's random source). -/
target platformHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "platform.c")
  buildO (pkg.buildDir / "rt" / "platform_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- A machine made of ordinary memory, for running the drivers as a process: one device window and some
shared memory, with the bare-metal device layer itself on top (rt/hosted/machine.c). -/
target machineHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "machine.c")
  buildO (pkg.buildDir / "rt" / "hosted" / "machine.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- Comparing and choosing in time that does not depend on secrets: `Secret.lean`, over a program in the small
language (`Mini/Secret.lean`). -/
@[default_target]
lean_lib Secret

/-- That program printed as C and compiled, for what runs on Lean's own runtime. (The minimal runtime prints
and compiles it with the rest, `scripts/print-runtime`.) -/
target secretHosted pkg : System.FilePath := do
  let some printer ← findLeanExe? `«mini-print» | error "no mini-print"
  let printed ← (← printer.fetch).mapM fun exe => do
    let c := pkg.buildDir / "printed" / "secret.c"
    IO.FS.createDirAll (pkg.buildDir / "printed")
    IO.FS.writeFile c (← captureProc { cmd := exe.toString, args := #["secret"] })
    return c
  buildO (pkg.buildDir / "printed" / "secret.o") printed
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- The runtime self-test: one pure function whose transcript must be the same on every runtime. -/
@[default_target]
lean_lib SelfTest

/-- Prints the self-test's transcript. Linked against each runtime in turn and the outputs compared. -/
@[default_target]
lean_exe «rt-test» where
  root := `RtTest
  moreLinkObjs := #[platformHosted, secretHosted]

/-- The big-number test's arithmetic and what it writes down, for the program of that name and for the probe. -/
@[default_target]
lean_lib BigTest

/-- The big-number test: arithmetic on numbers of 2^63 and above, written down as hashes. Linked against each
runtime in turn and the outputs compared. -/
@[default_target]
lean_exe «big-test» where
  root := `BigTestMain
  moreLinkObjs := #[platformHosted]

/-- The demo service over stdin/stdout on Lean's own runtime: the reference every other way of running it is
held to. -/
@[default_target]
lean_exe «demo-sim» where
  root := `DemoSim
  moreLinkObjs := #[platformHosted]

/-- The kernel's logic in Lean: for now the vsock protocol and the attestation device's messages, both as pure
functions of the bytes they are given. -/
@[default_target]
lean_lib Kernel

/-- The command line's words and a virtqueue's layout. Pure: no device. -/
@[default_target]
lean_exe «kernel-test» where
  root := `KernelTest

/-- The socket driver against a device that lies: a process in which the test is the device and writes what
it likes into the driver's queues. -/
@[default_target]
lean_exe «driver-test» where
  root := `DriverTest
  moreLinkObjs := #[machineHosted]

/-- Scenario tests and a fuzzer for the vsock protocol. Pure: no device. -/
@[default_target]
lean_exe «vsock-test» where
  root := `VsockTest

/-- Reports what the machine looks like and drives the devices it can without a parent. Only does anything on
bare metal (`scripts/build-bare virtio-probe`); as a process it finds no devices. -/
@[default_target]
lean_exe «virtio-probe» where
  root := `ProbeMain
  moreLinkObjs := #[platformHosted]

/-- The demo service as a whole machine: the socket device driver, the vsock protocol and the service. Only
does anything on bare metal (`scripts/build-bare silo-os`); as a process it finds no socket device. -/
@[default_target]
lean_exe «silo-os» where
  root := `OsMain
  moreLinkObjs := #[platformHosted]

/-- Turns a linked image into the kernel image a Linux boot protocol loader is given. Runs where the image is
built, not in it. -/
@[default_target]
lean_exe mkimage where
  root := `MkImage

/-- The attestation device's requests and responses, byte for byte, and noise. Pure: no device. -/
@[default_target]
lean_exe «nsm-test» where
  root := `NsmTest

/-- The pure tests of the framing and the commands. Run from the repo root. -/
@[default_target]
lean_exe «demo-test» where
  root := `DemoTest

/-- Reaching a demo service through a command's pipes: shared by the service's test and the parent's client. -/
@[default_target]
lean_lib Relay

/-- The parent's client: one request of a running service, through a relay such as socat. -/
@[default_target]
lean_exe ask where
  root := `Ask

/-- Drives a running demo service over its pipes and checks the replies: `sim-test <path to the service>`. -/
@[default_target]
lean_exe «sim-test» where
  root := `SimTest

target efiHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "efi.c")
  buildO (pkg.buildDir / "rt" / "efi_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

@[default_target]
lean_exe «tdx-os» where
  root := `TdxMain
  moreLinkObjs := #[platformHosted, efiHosted]

@[default_target]
lean_exe «net-internet-test» where
  root := `NetInternetTest

@[default_target]
lean_exe «net-tcp-test» where
  root := `NetTcpTest

lean_exe «net-flat-bench» where
  root := `NetFlatBench

@[default_target]
lean_exe «net-route-test» where
  root := `NetRouteTest

@[default_target]
lean_exe «net-dns-test» where
  root := `NetDnsTest

lean_exe «dns-probe» where
  root := `DnsProbe
  moreLinkObjs := #[platformHosted, efiHosted]
