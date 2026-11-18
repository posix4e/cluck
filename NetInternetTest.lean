import Kernel.Net.Internet

/-! Fixed Ethernet captures, independently encoded and decoded with tcpdump. All tests enter
the stack at its raw frame boundary, including malformed packets with a valid wire checksum. -/

open Kernel.Net.Internet

private def hex (text : String) : ByteArray := Id.run do
  let chars := text.toList.toArray
  let nibble (c : Char) := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let mut out := ByteArray.empty
  for i in [:chars.size / 2] do
    out := out.push (16 * nibble chars[2*i]! + nibble chars[2*i+1]!).toUInt8
  return out

private def arpRequest := hex "ffffffffffff525400654321080600010800060400015254006543210a0002020000000000000a00020f000000000000000000000000000000000000"
private def arpReply := hex "525400654321525400123456080600010800060400025254001234560a00020f5254006543210a000202000000000000000000000000000000000000"
private def udp4 := hex "52540012345652540065432108004500001f00004000401122be0a0002020a00020f9e6b138d000b566573696c000000000000000000000000000000"
private def udp6 := hex "52540012345652540065432186dd60000000000b1140fec00000000000000000000000000002fec000000000000000000000000000159e6b138d000b70dd73696c"
private def fragment4 := hex "52540012345652540065432108004500001f00002000401142be0a0002020a00020f9e6b138d000b566573696c000000000000000000000000000000"
private def icmp4 := hex "52540012345652540065432108004500002000004000400122cd0a0002020a00020f080014210102030473696c6f0000000000000000000000000000"
private def icmp4Reply := hex "52540065432152540012345608004500002000004000400122cd0a00020f0a00020200001c210102030473696c6f0000000000000000000000000000"
private def icmp6 := hex "52540012345652540065432186dd60000000000c3a40fec00000000000000000000000000002fec0000000000000000000000000001580009e410102030473696c6f"
private def icmp6Reply := hex "52540065432152540012345686dd60000000000c3a40fec00000000000000000000000000015fec0000000000000000000000000000281009d410102030473696c6f"
private def ndpRequest := hex "3333ff00001552540065432186dd6000000000203afffec00000000000000000000000000002ff0200000000000000000001ff0000158700e61600000000fec000000000000000000000000000150101525400654321"
private def ndpReply := hex "52540065432152540012345686dd6000000000203afffec00000000000000000000000000015fec000000000000000000000000000028800927860000000fec000000000000000000000000000150201525400123456"
private def dadRequest := hex "3333ff00001552540065432186dd6000000000183aff00000000000000000000000000000000ff0200000000000000000001ff00001587007bbd00000000fec00000000000000000000000000015"
private def dadWithMac := hex "3333ff00001552540065432186dd6000000000203aff00000000000000000000000000000000ff0200000000000000000001ff0000158700e4d900000000fec000000000000000000000000000150101525400654321"
private def dadReply := hex "33330000000152540012345686dd6000000000203afffec00000000000000000000000000015ff0200000000000000000000000000018800d23720000000fec000000000000000000000000000150201525400123456"
private def ndpBadOption := hex "3333ff00001552540065432186dd6000000000203afffec00000000000000000000000000002ff0200000000000000000001ff0000158700e61700000000fec000000000000000000000000000150100525400654321"
private def tcp6 := hex "52540012345652540065432186dd6000000000140640fec00000000000000000000000000002fec000000000000000000000000000159e6b138d000012340000000050022000ce1d0000"

private def guest : Config := { mac := hex "525400123456" }
private def host : Config where
  mac := hex "525400654321"
  ipv4 := hex "0a000202"
  ipv6 := hex "fec00000000000000000000000000002"

private def transmitted (event : Option Event) : Option ByteArray :=
  match event with | some (.transmit frame) => some frame | _ => none

private def resolved (event : Option Event) : Option Peer :=
  match event with | some (.neighbor peer) => some peer | _ => none

private def datagramMatches (event : Option Event) (ip : ByteArray) : Bool :=
  match event with
  | some (.udp peer src dst body) =>
    peer.mac == host.mac && peer.ip == ip && src == 40555 && dst == 5005 && body == "sil".toUTF8
  | _ => false

def main : IO UInt32 := do
  let failed ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      IO.eprintln s!"FAIL {name}"
      failed.modify (· + 1)
  let rx := receive guest
  let peer4 := { mac := guest.mac, ip := guest.ipv4 : Peer }
  let peer6 := { mac := guest.mac, ip := guest.ipv6 : Peer }
  check "RFC 1071 checksum example" (checksum (hex "0001f203f4f5f6f7") == 0x220d)
  check "zero-padded odd checksum" (checksum (hex "010203") == 0xfbfd)
  check "ARP solicitation" (solicit host guest.ipv4 == some arpRequest)
  check "ARP response" (transmitted (rx arpRequest) == some arpReply)
  check "ARP result" (resolved (receive host arpReply) == some peer4)
  check "ARP source mismatch" ((rx (arpRequest.set! 6 0x54)).isNone)
  check "ARP target MAC mismatch" ((receive host (arpReply.set! 32 0x54)).isNone)
  check "NDP solicitation" (solicit host guest.ipv6 == some ndpRequest)
  check "NDP response" (transmitted (rx ndpRequest) == some ndpReply)
  check "NDP result" (resolved (receive host ndpReply) == some peer6)
  check "DAD uses all-nodes and clears Solicited" (transmitted (rx dadRequest) == some dadReply)
  check "DAD with source link-layer address" ((rx dadWithMac).isNone)
  check "NDP zero-length option" ((rx ndpBadOption).isNone)
  check "NDP link hop limit" ((rx (ndpRequest.set! 21 254)).isNone)
  check "NDP multicast MAC mismatch" ((rx (ndpRequest.set! 5 16)).isNone)
  check "NDP truncation" ((rx (ndpRequest.extract 0 (ndpRequest.size-1))).isNone)
  check "ICMPv4 echo" (transmitted (rx icmp4) == some icmp4Reply)
  check "ICMPv6 echo" (transmitted (rx icmp6) == some icmp6Reply)
  check "ICMPv4 damaged checksum" ((rx (icmp4.set! 40 0)).isNone)
  check "ICMPv6 short body" ((rx (icmp6.extract 0 58)).isNone)
  check "UDP/IPv4 delivery ignores Ethernet padding" (datagramMatches (rx udp4) host.ipv4)
  check "UDP/IPv6 delivery" (datagramMatches (rx udp6) host.ipv6)
  check "IPv4 UDP omitted checksum" (datagramMatches (rx ((udp4.set! 40 0).set! 41 0)) host.ipv4)
  check "IPv6 UDP omitted checksum" ((rx ((udp6.set! 60 0).set! 61 0)).isNone)
  check "IPv4 fragmented packet at raw demux boundary" ((rx fragment4).isNone)
  check "IPv4 damaged header" ((rx (udp4.set! 22 63)).isNone)
  check "UDP truncated IPv4" ((rx (udp4.extract 0 44)).isNone)
  check "UDP inconsistent length" ((rx (((udp4.set! 39 12).set! 40 0).set! 41 0)).isNone)
  check "UDP forged transport checksum" ((rx (udp6.set! 62 0)).isNone)
  check "UDP/IPv4 wire format" (udpFrame host peer4 40555 5005 "sil".toUTF8 == some udp4)
  check "UDP/IPv6 wire format" (udpFrame host peer6 40555 5005 "sil".toUTF8 == some udp6)
  let big := ByteArray.mk (Array.replicate 1472 (0xa5 : UInt8))
  check "UDP/IPv4 MTU" ((udpFrame host peer4 40555 5005 big).isSome &&
    (udpFrame host peer4 40555 5005 (big.push 0)).isNone)
  check "UDP/IPv6 MTU" ((udpFrame host peer6 40555 5005 (big.extract 0 1452)).isSome &&
    (udpFrame host peer6 40555 5005 (big.extract 0 1453)).isNone)
  check "bad egress addresses" ((udpFrame host { peer4 with ip := hex "e0000001" } 40555 5005 big).isNone &&
    (solicit host (hex "ff")).isNone)
  let segment := tcp6.extract 54 tcp6.size
  check "TCP/IPv6 input checksum" (match rx tcp6 with
    | some (.tcp peer body) => peer.ip == host.ipv6 && body == segment
    | _ => false)
  check "TCP damaged data offset and checksum" ((rx (tcp6.set! 66 0)).isNone)
  check "TCP/IPv6 output checksum" (tcpFrame host peer6 ((segment.set! 16 0).set! 17 0) == some tcp6)
  -- Once the IPv6 packet's first byte is present, the IP length bounds every later read.
  for len in [:tcp6.size] do
    check s!"TCP capture truncated at {len}" ((rx (tcp6.extract 0 len)).isNone)
  let amount ← failed.get
  if amount != 0 then return 1
  IO.println "net-internet-test: all checks passed"
  return 0
