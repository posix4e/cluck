import Kernel.Net.Address

/-! Ethernet, IP and datagrams at the guest boundary. The NIC hands up one Ethernet frame at a
time, without its FCS. Endpoints have static addresses. A reply uses the link-layer source of the
request as its next hop, which covers clients on this link and clients reached through a router.
Handlers own no fragment queues, learned routes or peer-controlled caches. -/

namespace Kernel.Net.Internet

def mtu : Nat := 1500

private def broadcast : ByteArray := ⟨#[255,255,255,255,255,255]⟩
private def zeros (len : Nat) : ByteArray := ByteArray.mk (Array.replicate len (0 : UInt8))

private def be16 (n : Nat) : ByteArray :=
  ByteArray.empty.push (n >>> 8).toUInt8 |>.push n.toUInt8

/-- Callers check that both bytes are present. -/
private def get16 (buf : ByteArray) (i : Nat) : Nat :=
  (buf[i]!.toNat <<< 8) + buf[i+1]!.toNat

private def put16 (buf : ByteArray) (i n : Nat) : ByteArray :=
  (buf.set! i (n >>> 8).toUInt8).set! (i + 1) n.toUInt8

/-- RFC 1071 one's-complement checksum. An IP packet and pseudo-header fit in a 32-bit sum before folding. -/
def checksum (buf : ByteArray) : Nat := Id.run do
  let mut sum := 0
  for i in [:buf.size / 2] do
    sum := sum + get16 buf (2 * i)
  if buf.size % 2 == 1 then sum := sum + (buf[buf.size-1]!.toNat <<< 8)
  let folded := (sum &&& 0xffff) + (sum >>> 16)
  0xffff - ((folded &&& 0xffff) + (folded >>> 16))

def unicastMac (mac : ByteArray) : Bool :=
  mac.size == 6 && mac[0]! &&& 1 == 0 && mac != zeros 6

def unicast4 (ip : ByteArray) : Bool :=
  ip.size == 4 && ip[0]! != 0 && ip[0]! != 127 && ip[0]! < 224

def unicast6 (ip : ByteArray) : Bool :=
  ip.size == 16 && ip[0]! != 0xff && ip != zeros 16 &&
    ip != (zeros 15).push 1

private def multicastMac (ip : ByteArray) : ByteArray :=
  (ByteArray.mk #[0x33, 0x33]) ++ ip.extract 12 16

private def solicitedNode (ip : ByteArray) : ByteArray :=
  (ByteArray.mk #[0xff,2,0,0,0,0,0,0,0,0,0,1,0xff]) ++ ip.extract 13 16

private def ethernet (mac dst : ByteArray) (kind : Nat) (payload : ByteArray) : ByteArray :=
  let frame := dst ++ mac ++ be16 kind ++ payload
  frame ++ zeros (60 - frame.size)

def localIp (cfg : Config) (peer : Peer) : ByteArray :=
  if peer.ip.size == 4 then cfg.ipv4 else cfg.ipv6

def pseudo (src dst : ByteArray) (proto : UInt8) (len : Nat) : ByteArray :=
  let fields := if src.size == 4 then (ByteArray.mk #[0, proto]) ++ be16 len
                else zeros 2 ++ be16 len ++ (zeros 3).push proto
  src ++ dst ++ fields

def ipFrame (cfg : Config) (peer : Peer) (proto : UInt8) (body : ByteArray)
    (ttl : UInt8 := 64) : Option ByteArray := do
  guard (unicastMac cfg.mac)
  if peer.ip.size == 4 then
    guard (unicast4 cfg.ipv4 && unicast4 peer.ip && unicastMac peer.mac && body.size + 20 ≤ mtu)
    let head := (ByteArray.mk #[0x45,0]) ++ be16 (20 + body.size) ++
      (ByteArray.mk #[0,0,0x40,0,ttl,proto,0,0]) ++ cfg.ipv4 ++ peer.ip
    return ethernet cfg.mac peer.mac 0x0800 (put16 head 10 (checksum head) ++ body)
  else
    guard (unicast6 cfg.ipv6 && peer.ip.size == 16 && body.size + 40 ≤ mtu)
    guard ((unicast6 peer.ip && unicastMac peer.mac) ||
      (peer.ip[0]! == 0xff && peer.mac == multicastMac peer.ip))
    let head := (ByteArray.mk #[0x60,0,0,0]) ++ be16 body.size ++
      (ByteArray.mk #[proto, ttl]) ++ cfg.ipv6 ++ peer.ip
    return ethernet cfg.mac peer.mac 0x86dd (head ++ body)

private def transportFrame (cfg : Config) (peer : Peer) (proto : UInt8) (offset : Nat)
    (body : ByteArray) (ttl : UInt8 := 64) : Option ByteArray := do
  guard (body.size ≥ offset + 2 && body.size ≤ mtu)
  let body := put16 body offset 0
  let value := checksum (pseudo (localIp cfg peer) peer.ip proto body.size ++ body)
  let value := if proto == 17 && value == 0 then 0xffff else value
  ipFrame cfg peer proto (put16 body offset value) ttl

/-- Send a complete TCP segment. The Internet layer supplies its checksum. -/
def tcpFrame (cfg : Config) (peer : Peer) (segment : ByteArray) : Option ByteArray := do
  guard (segment.size ≥ 20)
  transportFrame cfg peer 6 16 segment

def udpFrame (cfg : Config) (peer : Peer) (srcPort dstPort : UInt16)
    (payload : ByteArray) : Option ByteArray := do
  guard (payload.size + 8 ≤ mtu && dstPort != 0)
  let head := be16 srcPort.toNat ++ be16 dstPort.toNat ++ be16 (payload.size + 8) ++ zeros 2
  transportFrame cfg peer 17 6 (head ++ payload)

inductive Event where
  | transmit (frame : ByteArray)
  | fragmentReply (peer : Peer) (proto : UInt8) (body : ByteArray)
  | tcp (peer : Peer) (segment : ByteArray)
  | udp (peer : Peer) (srcPort dstPort : UInt16) (payload : ByteArray)
  | neighbor (peer : Peer)

/-- Ask for the MAC of an on-link next hop. The caller matches replies against its own
outstanding solicitations. ARP and NDP provide reachability, without authenticating a peer. -/
def solicit (cfg : Config) (nextHop : ByteArray) : Option ByteArray := do
  guard (unicastMac cfg.mac)
  if nextHop.size == 4 then
    guard (unicast4 cfg.ipv4 && unicast4 nextHop)
    let req := (ByteArray.mk #[0,1,8,0,6,4,0,1]) ++ cfg.mac ++ cfg.ipv4 ++ zeros 6 ++ nextHop
    return ethernet cfg.mac broadcast 0x0806 req
  else
    guard (unicast6 nextHop)
    let dst := solicitedNode nextHop
    let req := (ByteArray.mk #[135,0,0,0,0,0,0,0]) ++ nextHop ++ (ByteArray.mk #[1,1]) ++ cfg.mac
    transportFrame cfg { mac := multicastMac dst, ip := dst } 58 2 req 255

private def arp (cfg : Config) (mac sender body : ByteArray) : Option Event := do
  guard (body.size ≥ 28 && body.extract 0 6 == ByteArray.mk #[0,1,8,0,6,4])
  guard (unicast4 cfg.ipv4 && body.extract 24 28 == cfg.ipv4 && body.extract 8 14 == sender)
  let ip := body.extract 14 18
  match get16 body 6 with
  | 1 =>
    -- An address probe carries an all-zero sender IP and still needs an answer (RFC 5227).
    guard (unicast4 ip || ip == zeros 4)
    let reply := (ByteArray.mk #[0,1,8,0,6,4,0,2]) ++ cfg.mac ++ cfg.ipv4 ++ sender ++ ip
    return .transmit (ethernet cfg.mac sender 0x0806 reply)
  | 2 =>
    guard (mac == cfg.mac && body.extract 18 24 == cfg.mac && unicast4 ip)
    return .neighbor { ip, mac := sender }
  | _ => none

private def datagram (peer : Peer) (dst : ByteArray) (proto : UInt8)
    (body : ByteArray) : Option Event := do
  let valid := fun () => checksum (pseudo peer.ip dst proto body.size ++ body) == 0
  if proto == 6 then
    guard (body.size ≥ 20 && valid ())
    return .tcp peer body
  else
    guard (proto == 17 && body.size ≥ 8 && get16 body 4 == body.size && get16 body 2 != 0)
    if get16 body 6 == 0 then guard (peer.ip.size == 4)
    else guard (valid ())
    return .udp peer (get16 body 0).toUInt16 (get16 body 2).toUInt16 (body.extract 8 body.size)

private def ipv4 (cfg : Config) (sender pkt : ByteArray) : Option Event := do
  -- Reject options, fragmented datagrams and the reserved fragment flag. Ethernet padding is
  -- outside the IP total length and never reaches the transport.
  guard (pkt.size ≥ 20 && pkt[0]! == 0x45 && pkt[8]! != 0 && get16 pkt 6 &&& 0xbfff == 0)
  let len := get16 pkt 2
  guard (20 ≤ len && len ≤ pkt.size && checksum (pkt.extract 0 20) == 0)
  let peer := { mac := sender, ip := pkt.extract 12 16 : Peer }
  guard (unicast4 peer.ip && unicast4 cfg.ipv4 && pkt.extract 16 20 == cfg.ipv4)
  let body := pkt.extract 20 len
  if pkt[9]! == 1 then
    guard (body.size ≥ 8 && get16 body 0 == 0x0800 && checksum body == 0)
    let reply := put16 (put16 body 0 0) 2 0
    let reply := put16 reply 2 (checksum reply)
    if 20 + reply.size > mtu then return .fragmentReply peer 1 reply
    return .transmit (← ipFrame cfg peer 1 reply)
  else datagram peer cfg.ipv4 pkt[9]! body

/-- Read up to one source or target link-layer address, skipping unknown well-formed options.
Each option advances by at least eight bytes. Reject duplicate or contradictory link addresses. -/
private def hasLinkAddress (body mac : ByteArray) (kind : UInt8) : Option Bool :=
  let rec loop : Nat → Nat → Bool → Option Bool
    | 0, pos, seen => if pos == body.size then some seen else none
    | fuel + 1, pos, seen => do
      if pos == body.size then return seen
      guard (pos + 2 ≤ body.size)
      let len := 8 * body[pos+1]!.toNat
      let wanted := body[pos]! == kind
      guard (len > 0 && pos + len ≤ body.size)
      guard (!wanted || (!seen && len == 8 && body.extract (pos+2) (pos+8) == mac))
      loop fuel (pos + len) (seen || wanted)
  loop ((body.size - 24) / 8 + 1) 24 false

private def neighborAdvert (cfg : Config) (peer : Peer) (dst body : ByteArray)
    (hopLimit : UInt8) : Option Event := do
  guard (hopLimit == 255 && body.size ≥ 24 && get16 body 0 == 0x8700 &&
    body.extract 8 24 == cfg.ipv6)
  let dad := peer.ip == zeros 16
  guard (if dad then dst == solicitedNode cfg.ipv6 else unicast6 peer.ip)
  let hasSource ← hasLinkAddress body peer.mac 1
  guard (!dad || !hasSource)
  let flags : UInt8 := if dad then 0x20 else 0x60
  let reply := (ByteArray.mk #[136,0,0,0,flags,0,0,0]) ++ cfg.ipv6 ++
    (ByteArray.mk #[2,1]) ++ cfg.mac
  let allNodes := (ByteArray.mk #[0xff,2]) ++ (zeros 13).push 1
  let dest := if dad then { ip := allNodes, mac := multicastMac allNodes : Peer } else peer
  return .transmit (← transportFrame cfg dest 58 2 reply 255)

private def ipv6 (cfg : Config) (mac sender pkt : ByteArray) : Option Event := do
  guard (unicast6 cfg.ipv6 && pkt.size ≥ 40 && pkt[0]! >>> 4 == 6 && pkt[7]! != 0)
  let len := 40 + get16 pkt 4
  guard (len ≤ pkt.size)
  let dst := pkt.extract 24 40
  let unicast := dst == cfg.ipv6 && mac == cfg.mac
  guard (unicast || (dst == solicitedNode cfg.ipv6 && mac == multicastMac dst))
  let peer := { mac := sender, ip := pkt.extract 8 24 : Peer }
  let body := pkt.extract 40 len
  let proto := pkt[6]!
  if proto == 58 then
    guard (body.size ≥ 4 && checksum (pseudo peer.ip dst proto body.size ++ body) == 0)
    if body[0]! == 135 then neighborAdvert cfg peer dst body pkt[7]!
    else if body[0]! == 136 then
      guard (unicast && pkt[7]! == 255 && body.size ≥ 24 && body[1]! == 0 &&
        body[4]! &&& 0x40 != 0 && unicast6 peer.ip)
      let target := body.extract 8 24
      guard (unicast6 target && (← hasLinkAddress body sender 2))
      return .neighbor { ip := target, mac := sender }
    else
      guard (unicast && unicast6 peer.ip && body.size ≥ 8 && get16 body 0 == 0x8000)
      let reply := put16 (body.set! 0 129) 2 0
      if 40 + reply.size > mtu then
        let sum := checksum (pseudo cfg.ipv6 peer.ip 58 reply.size ++ reply)
        return .fragmentReply peer 58 (put16 reply 2 sum)
      return .transmit (← transportFrame cfg peer 58 2 reply)
  else
    guard (unicast && unicast6 peer.ip)
    datagram peer cfg.ipv6 proto body

/-- Consume one raw Ethernet frame. Only complete untagged frames addressed to this endpoint
are delivered. The protocol-specific readers check lengths before indexing wire bytes. -/
def receiveReassembled (cfg : Config) (frame : ByteArray) : Option Event := do
  guard (unicastMac cfg.mac && frame.size ≥ 14 && frame.size ≤ 14 + 40 + 65535)
  let mac := frame.extract 0 6
  let sender := frame.extract 6 12
  guard (unicastMac sender)
  let body := frame.extract 14 frame.size
  match get16 frame 12 with
  | 0x0806 => do guard (mac == cfg.mac || mac == broadcast); arp cfg mac sender body
  | 0x0800 => do guard (mac == cfg.mac); ipv4 cfg sender body
  | 0x86dd => ipv6 cfg mac sender body
  | _ => none

def receive (cfg : Config) (frame : ByteArray) : Option Event := do
  guard (frame.size ≤ 14 + mtu)
  receiveReassembled cfg frame

end Kernel.Net.Internet
