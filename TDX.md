# Intel TDX guest

The x86-64 guest boots as `EFI/BOOT/BOOTX64.EFI` and runs the project’s minimal
Lean runtime. TDVF drives the virtio PCI NIC and supplies raw Ethernet frames
through the UEFI Simple Network Protocol. Lean handles Ethernet, IP, TCP and UDP
inside the guest. QEMU’s user network backend provides a virtual link and port
forwarding on the host.

## Run the prebuilt guest

The source-and-images archive includes the tested EFI applications and combined TDVF.
Extract it on a TDX-enabled x86-64 Linux host with QEMU and run the launcher.

```sh
tar -xzf silo-tdx-x86_64.tar.gz
cd silo-tdx
sha256sum -c SHA256SUMS
scripts/run-efi tdx
```

For a hardware smoke test of the prebuilt archive, stop the interactive guest and run
`scripts/test-efi tdx --selftest 0cd88f4540d6430b` followed by
`scripts/test-efi-ipv6 tdx`. Each test launches and stops its own guest.

From a second terminal while the interactive guest is running, this request should print `000000068168656c6c6f`.
The reply contains a big-endian length, the ping reply opcode, and the word `hello`.

```sh
python3 - <<'PING'
import socket
with socket.create_connection(("127.0.0.1", 5005), timeout=5) as sock:
    sock.sendall(bytes.fromhex("000000060168656c6c6f"))
    print(sock.makefile("rb").read(10).hex())
PING
```

## Build and run locally

Use the Lean version pinned in `lean-toolchain`. On an x86-64 Linux builder,
the installed Lean toolchain supplies the target archives. On macOS or Arm Linux,
point `SILO_LINUX_TOOLCHAIN` at the unpacked x86-64 Linux release of that same
Lean version, as for `scripts/build-bare`.

```sh
lake build
scripts/build-efi dev
scripts/build-efi tdx
scripts/test-efi
scripts/test-efi-ipv6
```

To keep the development guest running, use `scripts/run-efi dev`. It uses TCG
and OVMF. Set `SILO_OVMF_CODE` and `SILO_OVMF_VARS` to a matched x64 flash
pair when QEMU installs them outside the launcher's search paths. In a second
terminal, send a framed request over TCP.

```sh
.lake/build/bin/ask ping hello -- socat - TCP:127.0.0.1:5005
```

Port 5005 accepts the existing length-prefixed demo protocol over TCP and
echoes one datagram per request over UDP. Both forwards bind to loopback.
`SILO_HOST_PORT` changes the host port for both protocols. The guest’s static
addresses are `10.0.2.15` and `fec0::15`, the development network’s guest
addresses. Set `Internet.Config` in `TdxMain.lean` when building for another
network. `SILO_NET_SOCKET=/path/to/link.sock` selects a QEMU UNIX stream Ethernet
backend for a point-to-point link. The IPv6 integration test drives that link.

## Build the firmware for TDX

The IntelTdxX64 firmware manifest in the revision below ships virtio PCI and
block drivers. The supplied patch includes `VirtioNetDxe` in the firmware volume
so the application can open the raw Ethernet protocol. The second patch validates
virtqueue completions in release builds and indexes driver-owned buffer metadata. Build on Linux with a C/C++
toolchain, GNU make, Python 3, NASM, iASL and the libuuid development headers.

```sh
SILO_ROOT="$PWD"
git clone https://github.com/tianocore/edk2.git edk2
cd edk2
git checkout 556dcfb466e9f05affeaff881d738807f8156d3c
git submodule update --init --depth=1
git apply "$SILO_ROOT/boot/efi/tdvf-net.patch"
git apply "$SILO_ROOT/boot/efi/tdvf-net-completions.patch"
make -C BaseTools/Source/C -j8
. edksetup.sh
export SOURCE_DATE_EPOCH=$(git log -1 --format=%ct)
build -a X64 -b RELEASE -t GCC -n 8 -p OvmfPkg/IntelTdx/IntelTdxX64.dsc
export SILO_TDVF="$PWD/Build/IntelTdx/RELEASE_GCC/FV/OVMF.fd"
cd "$SILO_ROOT"
```

## Boot on Intel hardware

The host needs Intel TDX enabled in the platform and KVM, permission to use
`/dev/kvm`, and a QEMU build exposing `tdx-guest`. The launcher uses the combined
TDVF image with `-bios`, a q35 machine, split irqchip, one vCPU, and modern virtio
devices with `iommu_platform=on`. The newly built firmware starts with an empty
key store. For a deployment that enforces Secure Boot, enroll the intended
signing keys and sign the application. Firmware, its key store and boot policy
are part of the trust decision. [QEMU TDX launch requirements](https://www.qemu.org/docs/master/system/i386/tdx.html)

```sh
SILO_TDVF=/path/to/OVMF.fd scripts/run-efi tdx
```

`scripts/test-efi tdx` and `scripts/test-efi-ipv6 tdx` each start a fresh hardware
guest and terminate it after the test. The first compares the guest’s self-test
with `.lake/build/bin/demo-sim`. On a hardware host without Lean, pass
`--selftest <eight-byte digest in hex>` from the corresponding hosted build.

## TDX evidence

TCP command `05` takes exactly 64 bytes of REPORTDATA. The hardware response is
`85` followed by the 1024-byte local TDREPORT. The development guest returns the
demo’s unavailable refusal. TCP command `02` is the existing Nitro attestation
command and is unavailable on this target.

On the machine running the TD, the helper below requests the report over the
forwarded TCP port and submits it to Intel’s QGS UNIX socket. The argument is
128 hex digits of REPORTDATA from the verifier. `--host`, `--port` and `--qgs`
override the default endpoints. The output file must be new.

```sh
scripts/tdx-quote "$REPORTDATA_HEX" quote.bin
```

On a separate trusted x86-64 Linux verifier with Intel DCAP QVL and its quote provider
configured, the included verifier checks the quote against a fresh challenge and
your known-good measurements. The archive contains `measurements.json` for the
tested firmware, image and QEMU boot configuration. Establish its provenance
independently, or supply your own reference policy for your deployment.

```sh
verify/verify-tdx-quote quote.bin --reportdata "$REPORTDATA_HEX" --measurements measurements.json
```

The relying party verifies the signed quote, collateral, freshness, DEBUG bit,
and expected MRTD and RTMR values, including the measured EFI application. A quote
from this command alone establishes neither a trusted application identity nor an
authenticated network session. [Intel DCAP quoting library](https://download.01.org/intel-sgx/latest/dcap-latest/linux/docs/Intel_TDX_DCAP_Quoting_Library_API.pdf)

## Using the stack from a service

- `Kernel.Efi` supplies the NIC MAC, whole-frame receive and transmit, and a
  monotonic timer. EFI boot services stay active for the lifetime of the guest.
- `Kernel.Net.Internet` validates link and network headers, transport checksums
  and destination addresses. It answers ARP, Neighbor Discovery and ICMP echo.
- `Kernel.Net.Fragment` provides bounded IP reassembly and fragmented UDP output.
  A conflicting fragment invalidates its datagram. The link MTU is 1500.
- `Kernel.Net.Route` selects the on-link destination or default router for
  outbound packets. A lookup returns a peer, an ARP/ND frame to transmit, a
  pending lookup or an unreachable result. Pass a corresponding neighbor reply
  to `Neighbors.learn` and retry the lookup. The IP destination stays the remote
  endpoint when the Ethernet destination is the router.
- `Kernel.Net.Tcp` exposes connection, stream data, half-close and close events.
  Its send and timer operations return wire segments for the Internet layer.
  Address and port keys distinguish independent connections. `TdxMain.lean`
  shows how to drive the stack and maintain one demo decoder per TCP stream.

For an outbound DNS lookup, call `Dns.Query.start` with a resolver IP, unused
ephemeral UDP port, random transaction ID, name, and `.a` or `.aaaa`. Drive
`Query.step` with incoming Internet events and monotonic time. It emits ARP or
NDP and UDP frames and returns addresses or a terminal error. The resolver
accepts bounded CNAME chains and reports truncated replies. To exercise the
outbound path through QEMU’s resolver, build and boot the probe.

```sh
scripts/build-efi dev dns-probe
scripts/run-efi dev dns-probe
```

This profile uses static addresses and routes. Automatic address configuration,
DNSSEC, DNS over TCP, TLS and a POSIX socket ABI remain outside its scope. IPv4 options and general IPv6 extension
chains are outside the implemented packet profile. The stack is a single-threaded
Lean library in the unikernel address space.
