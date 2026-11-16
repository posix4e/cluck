# What a Nitro Enclave looks like to the image

Recorded on 2026-11-15 from a real enclave: an m5.xlarge parent in us-east-2 (Intel Xeon Platinum 8175M,
Amazon Linux 2023, `nitro-cli` 1.5.0), the enclave given 2 CPUs and 512 MiB. The image was
`virtio-probe.eif`, started in debug mode with the command line `silo.heartbeat=3:9000 silo.report`, and this
is what it printed on the console:

```
silo boot: entered by the Linux boot protocol at its 64-bit entry, loaded at 0x0000000000100000
silo boot: memory at 0x0000000000000000 of 0x000000000009fc00 bytes, kind 0x0000000000000001
silo boot: memory at 0x0000000000100000 of 0x000000001f6fffff bytes, kind 0x0000000000000001
silo boot: heap at 0x0000000002200000 of 0x000000001d400000 bytes
silo boot: device registers at 0x00000000d0000000 of 0x0000000000001000 bytes
silo boot: device registers at 0x00000000d0001000 of 0x0000000000001000 bytes
probe: heartbeat answered by 3:9000
probe: command line: silo.heartbeat=3:9000 silo.report virtio_mmio.device=4K@0xd0000000:5 virtio_mmio.device=4K@0xd0001000:6
probe: 2 register windows announced
probe: window at 0xd0000000 of 4096 bytes: magic 0x74726976, version 2, device 19, vendor 0x0
probe: window at 0xd0001000 of 4096 bytes: magic 0x74726976, version 2, device 33, vendor 0x0
probe: virtio device 19 at 0xd0000000
probe: socket device with address 16
probe: virtio device 33 at 0xd0001000
probe: secure module queue of 4 entries
probe: secure module random 2c42fecf1412b8c3d600dad70a77ed48c09a841d25c7e8ae4e838ae8cf98bc65
probe: attestation document of 4461 bytes, starting 8444a1013822a0591101bf696d6f6475
probe: the secure module works
```

What that says, and what the code relies on:

- **Entry.** The loader uses the Linux boot protocol's 64-bit entry and puts the kernel proper at 1 MiB. The
  image then moves itself to 16 MiB (`linux.S`). The real-mode code in `setup.S` never runs.
- **Memory.** Two usable ranges, the usual one below 640 KiB and one from 1 MiB to the end of what the
  enclave was given, with about 9 MiB of the 512 held back. The heap is everything in the second range above
  the image.
- **Devices.** Two, announced on the kernel command line after the image's own words, the way Linux is told
  about memory-mapped virtio devices: the socket (virtio device 19) at `0xd0000000` and the Secure Module
  (33) at `0xd0001000`, each 4 KiB, both speaking version 2 of the register layout. There is no entropy
  device and nothing else.
- **Addresses.** The parent is address 3. The enclave's own address is whatever `nitro-cli` was told (16
  here).
- **The heartbeat** to 3:9000 is what makes `nitro-cli run-enclave` return. It is answered with the same
  byte.
- **The Secure Module's queue** has 4 entries (QEMU's emulation has 2); the driver uses 2.
- **An attestation document** is about 4.5 KiB. Its content is written as an open-ended CBOR map (the `bf`
  in the bytes above), which `verify/verify-attestation` has to accept.
- **The console** is the first serial port. It can be read only when the enclave was started in debug mode,
  and then its attestation has all-zero measurements.

To do it again, from an enclave-enabled instance with `aws-nitro-enclaves-cli` and `socat` installed and the
allocator service running, with the files CI keeps (`silo-os-enclave-image`):

```
sudo nitro-cli run-enclave --eif-path virtio-probe.eif --cpu-count 2 --memory 512 --enclave-cid 16 --debug-mode
sudo nitro-cli console --enclave-name virtio-probe

sudo nitro-cli run-enclave --eif-path silo-os.eif --cpu-count 2 --memory 512 --enclave-cid 17
./sim-test --socket socat - VSOCK-CONNECT:17:5005
./ask attest <nonce in hex> document.bin -- socat - VSOCK-CONNECT:17:5005
```

and then, anywhere else, `verify/verify-attestation --document document.bin --nonce <the same> --pcrs
silo-os.pcrs.json`.

## The second run: what the processor offers

On 2026-11-16 `virtio-probe.eif` ran in debug mode on an m6i.xlarge in us-east-2 (Intel Xeon Platinum 8375C),
given 1,024 MiB. It was entered and laid out as before, and its report had one new line:

```
silo boot: timing that does not depend on data: turned on
```

So an enclave on that processor is offered the mode and keeps it once set. The same run tried the images
that check the memory mapping and the big-number test (`scripts/enclave-checks`) and learned only this:
an image that does not answer the boot heartbeat shows nothing on its console before `nitro-cli` takes it
down, even started with the console attached.

## The third run: what the machine refuses

Later on 2026-11-16, on another m6i.xlarge, `scripts/enclave-checks` started the probe eleven more times in
debug mode, each told on its command line one thing to try after the heartbeat. All ten things the memory
mapping forbids were refused as they are under QEMU, for example:

```
silo boot: writing 0x000000000100adb0, which that memory does not allow
silo boot: reading 0x00000000d0002000, which is not mapped
silo boot: writing 0x0000000001396ff8, the hole under the stack: the stack overflowed
```

and the big-number test printed what it prints on Lean's own runtime. An enclave that has stopped itself is
not taken down: its console stays attached until the parent ends it, so each check takes as long as the
script is willing to wait (two minutes).
