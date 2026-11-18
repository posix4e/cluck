import Kernel.Efi
import Kernel.Net.Dns

/-! A service using DNS over the QEMU user network. The A records for ipv4only.arpa. are
specified by RFC 7050. The Ethernet loop still answers ARP while it waits for the DNS server. -/

open Kernel Kernel.Net

private partial def run (cfg : Internet.Config) (query : Dns.Query) : IO UInt32 := do
  let now := (← Efi.millis).toNat
  let frame ← Efi.receive
  let event := Internet.receive cfg frame
  if let some (.transmit reply) := event then Efi.send reply
  let (query, action) := query.step now cfg {} event
  match action with
  | .transmit frame => Efi.send frame
  | .done (.addresses ips) =>
    let passed := ips.contains (ByteArray.mk #[192,0,0,170]) && ips.contains (ByteArray.mk #[192,0,0,171])
    let msg := if passed then "silo: DNS resolved ipv4only.arpa. to both RFC 7050 addresses\n"
               else "silo: DNS address set differs from RFC 7050\n"
    Platform.write msg.toUTF8
    return if passed then 0 else 3
  | .done _ =>
    Platform.write "silo: DNS lookup did not return addresses\n".toUTF8
    return 4
  | .wait => if frame.isEmpty then Efi.idle
  run cfg query

def main : IO UInt32 := do
  let mac ← Efi.mac
  if mac.size != 6 then return 1
  let entropy ← Platform.random 4
  if entropy.size != 4 then return 1
  let id := (256 * entropy[0]!.toNat + entropy[1]!.toNat).toUInt16
  let port := (49152 + (256 * entropy[2]!.toNat + entropy[3]!.toNat) % 16384).toUInt16
  let some q := Dns.Query.start (← Efi.millis).toNat ⟨#[10,0,2,3]⟩ port id "ipv4only.arpa." .a
    | return 2
  run { mac } q
