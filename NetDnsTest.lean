import Kernel.Net.Dns

/-! Exercise the resolver over two Ethernet endpoints and DNS wire records, including
out-of-order answer records, label compression, endpoint matching, retries and deadlines. -/

open Kernel.Net

private def client : Internet.Config where
  mac := ⟨#[2,0,0,0,0,1]⟩

private def server : Internet.Config where
  mac := ⟨#[2,0,0,0,0,2]⟩
  ipv4 := ⟨#[10,0,2,3]⟩
  ipv6 := ⟨#[0xfe,0xc0,0,0,0,0,0,0,0,0,0,0,0,0,0,3]⟩

private def started (kind : Dns.Kind := .a) (ipv6 : Bool := false) :
    Option (Dns.Query × ByteArray × Internet.Peer) := do
  let resolver := if ipv6 then server.ipv6 else server.ipv4
  let q ← Dns.Query.start 0 resolver 53333 0x5678 "Host.Example." kind
  let (q, .transmit arp) := q.step 0 client {} none | none
  let .transmit reply ← Internet.receive server arp | none
  let event ← Internet.receive client reply
  let (q, .transmit frame) := q.step 1 client {} (some event) | none
  let .udp peer 53333 53 msg ← Internet.receive server frame | none
  return (q, msg, peer)

private def queryTail (kind : Dns.Kind) : ByteArray :=
  (ByteArray.mk #[4]) ++ "host".toUTF8 ++ (ByteArray.mk #[7]) ++ "example".toUTF8 ++
    (ByteArray.mk #[0,0, if kind == .a then 1 else 28,0,1])

private def response (kind : Dns.Kind) (answers : UInt8) (flags : UInt16 := 0x8180) : ByteArray :=
  (ByteArray.mk #[0x56,0x78,(flags >>> 8).toUInt8,flags.toUInt8,0,1,0,answers,0,0,0,0]) ++ queryTail kind

private def address : ByteArray := ⟨#[203,0,113,7]⟩
private def rrA : ByteArray := ByteArray.mk #[0xc0,0x0c,0,1,0,1,0,0,0,60,0,4] ++ address

private def deliver (q : Dns.Query) (peer : Internet.Peer) (msg : ByteArray) : Option Dns.Answer := do
  let frame ← Internet.udpFrame server peer 53 53333 msg
  let event ← Internet.receive client frame
  let (_, .done answer) := q.step 2 client {} (some event) | none
  return answer

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (label : String) (ok : Bool) := do
    unless ok do
      IO.eprintln s!"FAIL {label}"
      failures.modify (· + 1)
  let some (q, query, peer) := started | IO.eprintln "ARP, route or UDP failed"; return 1
  check "wire question" (query == (ByteArray.mk #[0x56,0x78,1,0,0,1,0,0,0,0,0,0]) ++ queryTail .a)
  let standard := response .a 1 ++ rrA
  check "A response" (deliver q peer standard == some (.addresses #[address]))
  let canon := (ByteArray.mk #[6]) ++ "server".toUTF8 ++ (ByteArray.mk #[0xc0,17])
  let canonicalA := canon ++ rrA.extract 2 rrA.size
  let alias := ByteArray.mk #[0xc0,12,0,5,0,1,0,0,0,60,0,2,0xc0,30]
  check "CNAME chain with compressed RDATA and reversed records"
    (deliver q peer (response .a 2 ++ canonicalA ++ alias) == some (.addresses #[address]))
  check "unrelated answer is ignored" (deliver q peer (response .a 1 ++ canonicalA) == some .noData)
  check "CNAME cycle" ((deliver q peer (response .a 1 ++ (alias.set! 13 12))).isNone)
  check "compression pointer to itself" ((deliver q peer (response .a 1 ++ (rrA.set! 1 30))).isNone)
  check "truncated A RDATA" ((deliver q peer (standard.extract 0 (standard.size-1))).isNone)
  check "changed echoed question" ((deliver q peer (standard.set! 13 65)).isNone)
  check "mismatched ID" ((deliver q peer (standard.set! 1 0)).isNone)
  check "invalid opcode" ((deliver q peer (standard.set! 2 0x91)).isNone)
  check "negative response" (deliver q peer (response .a 0 0x8183) == some (.serverError 3))
  check "truncation signalled" (deliver q peer (response .a 8 0x8380) == some .truncated)
  check "record count bounded" ((deliver q peer (response .a 255)).isNone)
  check "response bound" ((deliver q peer (standard ++ ByteArray.mk (Array.replicate 512 0))).isNone)
  let resolver := { ip := server.ipv4, mac := server.mac : Internet.Peer }
  let waits := fun input => match (q.step 2 client {} (some input)).2 with | .wait => true | _ => false
  check "remote IP" (waits (.udp { resolver with ip := client.ipv4 } 53 53333 standard))
  check "source port" (waits (.udp resolver 54 53333 standard))
  check "local port" (waits (.udp resolver 53 53334 standard))
  check "no early retry" (match (q.step 999 client {} none).2 with | .wait => true | _ => false)
  check "UDP retransmit" (match (q.step 1001 client {} none).2 with
    | .transmit f => match Internet.receive server f with | some (.udp _ 53333 53 b) => b == query | _ => false
    | _ => false)
  check "deadline wins over late reply" (match (q.step 5000 client {} (some (.udp resolver 53 53333 standard))).2 with
    | .done .timeout => true | _ => false)
  let some (q6, _, peer) := started .aaaa | IO.eprintln "AAAA query failed"; return 1
  let v6 := ByteArray.mk #[0x20,1,0x0d,0xb8,0,0,0,0,0,0,0,0,0,0,0,7]
  let rr := ByteArray.mk #[0xc0,12,0,28,0,1,0,0,0,60,0,16] ++ v6
  check "AAAA over IPv4 resolver transport" (deliver q6 peer (response .aaaa 1 ++ rr) == some (.addresses #[v6]))
  let some (dual, _, peer6) := started .aaaa true | IO.eprintln "IPv6 DNS route failed"; return 1
  check "AAAA through IPv6 NDP and UDP" (peer6.ip == client.ipv6 &&
    deliver dual peer6 (response .aaaa 1 ++ rr) == some (.addresses #[v6]))
  check "wrong question kind" ((deliver q6 peer standard).isNone)
  for name in ["", ".", ".bad", "bad..name", "bad..", "has space", String.ofList (List.replicate 64 'a')] do
    check s!"reject invalid hostname {name}" ((Dns.Query.start 0 server.ipv4 53333 0 name .a).isNone)
  check "reject service source port" ((Dns.Query.start 0 server.ipv4 53 0 "host" .a).isNone)
  if (← failures.get) != 0 then return 1
  IO.println "net-dns-test: all checks passed"
  return 0
