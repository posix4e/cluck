import Kernel.Net.Internet

/-! IP fragmentation on an Ethernet link with MTU 1500. Reassembly retains
bounded, disjoint pieces in private memory. At most one minute of incomplete
traffic survives. A conflicting fragment invalidates the entire datagram. -/

namespace Kernel.Net.Fragment

open Internet

private def get16 (b : ByteArray) (at_ : Nat) : Nat :=
  b[at_]!.toNat * 256 + b[at_ + 1]!.toNat

private def be16 (v : Nat) : ByteArray := ⟨#[(v / 256).toUInt8, v.toUInt8]⟩
private def put16 (b : ByteArray) (pos v : Nat) : ByteArray :=
  (b.set! pos (v / 256).toUInt8).set! (pos+1) v.toUInt8

private structure Key where
  addrs : ByteArray
  id : ByteArray
  proto : UInt8
  deriving BEq

private structure Piece where
  start : Nat
  data : ByteArray

private structure Incoming extends Piece where
  key : Key
  header : ByteArray
  last : Bool
  maximum : Nat

private structure Assembly where
  key : Key
  expires : Nat
  pieces : Array Piece := #[]
  header : ByteArray := ByteArray.empty
  length : Option Nat := none
  total : Nat := 0
  rejected : Bool := false

structure Cache where
  private assemblies : Array Assembly := #[]

private def parse (cfg : Config) (frame : ByteArray) : Option Incoming := do
  guard (frame.size ≥ 34 && frame.size ≤ 14 + mtu && frame.extract 0 6 == cfg.mac)
  guard (Internet.unicastMac (frame.extract 6 12))
  let v4 := get16 frame 12 == 0x0800
  if v4 then
    guard (frame[14]! == 0x45 && frame[22]! != 0 && frame.extract 30 34 == cfg.ipv4)
    guard (Internet.unicast4 (frame.extract 26 30) && (frame[23]! == 1 || frame[23]! == 6 || frame[23]! == 17))
    let len := get16 frame 16
    guard (len ≥ 20 && len + 14 ≤ frame.size && checksum (frame.extract 14 34) == 0)
    let flags := get16 frame 20
    guard (flags > 0 && flags < 0x4000)
    let key := { addrs := frame.extract 26 34, id := frame.extract 18 20, proto := frame[23]! }
    return { key, header := frame.extract 0 34, start := (flags % 0x2000) * 8,
             last := flags < 0x2000, data := frame.extract 34 (14+len), maximum := 65515 }
  else
    guard (get16 frame 12 == 0x86dd && frame.size ≥ 62 && frame[14]! >>> 4 == 6 &&
      frame[20]! == 44 && frame[21]! != 0 && frame.extract 38 54 == cfg.ipv6)
    guard (Internet.unicast6 (frame.extract 22 38))
    let len := get16 frame 18
    guard (len ≥ 8 && 54 + len ≤ frame.size)
    let frag := get16 frame 56
    guard ((frag &&& 0xfff8) != 0 || frame[54]! == 6 || frame[54]! == 17 || frame[54]! == 58)
    let key := { addrs := frame.extract 22 54, id := frame.extract 58 62, proto := 44 }
    return { key, header := (frame.extract 0 54).set! 20 frame[54]!,
             start := frag &&& 0xfff8, last := frag % 2 == 0,
             data := frame.extract 62 (54+len), maximum := 65535 }

private def makeFrame (header body : ByteArray) : ByteArray :=
  if header.size == 34 then
    let h := put16 (put16 (put16 header 16 (20 + body.size)) 20 0) 24 0
    put16 h 24 (checksum (h.extract 14 34)) ++ body
  else put16 header 18 body.size ++ body

private def overlap (a b : Piece) : Bool :=
  a.start < b.start + b.data.size && b.start < a.start + a.data.size

private def assemble (a : Assembly) (f : Incoming) : Assembly := Id.run do
  if a.rejected then return a
  let finish := f.start + f.data.size
  let length := if f.last then some finish else a.length
  let conflict := a.pieces.size ≥ 128 || a.pieces.any (overlap f.toPiece) ||
    (f.last && a.length.isSome) || a.length.any (fun n => finish ≥ n && !f.last) ||
    (f.last && a.pieces.any (fun p => p.start + p.data.size > finish))
  if conflict then return { key := a.key, expires := a.expires, rejected := true }
  return { a with
    pieces := a.pieces.push f.toPiece
    length
    total := a.total + f.data.size
    header := if f.start == 0 then f.header else a.header }

private def deliver (cfg : Config) (h body : ByteArray) : Option Event := do
  -- RFC 6980 excludes fragmented Neighbor Discovery, including atomic fragments.
  if h.size == 54 && h[20]! == 58 then
    guard (body.size ≥ 8 && !(133 ≤ body[0]!.toNat && body[0]!.toNat ≤ 137))
  Internet.receiveReassembled cfg (makeFrame h body)

private def complete (a : Assembly) : Option ByteArray := do
  let len ← a.length
  guard (len == a.total && !a.header.isEmpty)
  let mut out := ByteArray.emptyWithCapacity len
  for _ in [:a.pieces.size] do
    let p ← a.pieces.find? (·.start == out.size)
    out := out ++ p.data
  guard (out.size == len)
  return out

def Cache.expire (cache : Cache) (now : Nat) : Cache :=
  { assemblies := cache.assemblies.filter (·.expires > now) }

/-- Deliver the transport event exactly once when the last missing fragment
arrives. Packets without a fragment header use the normal MTU-checked path. -/
def Cache.receive (cache : Cache) (now : Nat) (cfg : Config) (frame : ByteArray) :
    Cache × Option Event := Id.run do
  let some frag := parse cfg frame | return (cache, Internet.receive cfg frame)
  if frag.start + frag.data.size > frag.maximum || frag.data.isEmpty ||
      (!frag.last && frag.data.size % 8 != 0) then return (cache, none)
  if frag.start == 0 && frag.header.size == 54 then
    -- RFC 7112 requires the first fragment to include the upper-layer header.
    if frag.data.size < 8 || (frag.header[20]! == 6 &&
        (frag.data.size < 20 || frag.data.size < (frag.data[12]!.toNat / 16) * 4)) then
      return (cache, none)
  if frag.start == 0 && frag.last then return (cache, deliver cfg frag.header frag.data)
  let live := cache.assemblies.filter (·.expires > now)
  let old := live.find? (·.key == frag.key)
  if old.isNone && live.size ≥ 8 then return ({ assemblies := live }, none)
  let a := assemble (old.getD { key := frag.key, expires := now + 60000 }) frag
  let others := live.filter (·.key != frag.key)
  if let some whole := complete a then
    return ({ assemblies := others }, deliver cfg a.header whole)
  return ({ assemblies := others.push a }, none)

/-- Split a transport packet whose checksum already covers the whole body. -/
def ipFrames (cfg : Config) (peer : Peer) (proto : UInt8) (datagram : ByteArray)
    (id : UInt32) : Array ByteArray := Id.run do
  let v4 := peer.ip.size == 4
  let len := datagram.size
  if let some frame := ipFrame cfg peer proto datagram then return #[frame]
  if len > (if v4 then 65515 else 65535) then return #[]
  let some template := ipFrame cfg peer proto ByteArray.empty | return #[]
  let header := template.extract 0 (if v4 then 34 else 54)
  let chunk := if v4 then 1480 else 1448
  let mut frames := #[]
  for i in [:(len + chunk - 1) / chunk] do
    let offset := i * chunk
    let piece := datagram.extract offset (offset + chunk)
    let more := offset + piece.size < len
    if v4 then
      let h := put16 (put16 header 16 (20 + piece.size)) 18 id.toNat
      let h := put16 (put16 h 20 ((if more then 0x2000 else 0) + offset / 8)) 24 0
      frames := frames.push (put16 h 24 (checksum (h.extract 14 34)) ++ piece)
    else
      let h := (put16 header 18 (8 + piece.size)).set! 20 44
      let fh := ByteArray.mk #[proto, 0] ++ be16 (offset + (if more then 1 else 0)) ++
        be16 (id.toNat / 65536) ++ be16 id.toNat
      frames := frames.push (h ++ fh ++ piece)
  return frames

/-- Create the datagram checksum before splitting it. Each non-final fragment
ends on an eight-byte boundary. The caller supplies a fresh identification. -/
def udpFrames (cfg : Config) (peer : Peer) (src dst : UInt16)
    (payload : ByteArray) (id : UInt32) : Array ByteArray := Id.run do
  if let some frame := udpFrame cfg peer src dst payload then return #[frame]
  let v4 := peer.ip.size == 4
  if payload.size > (if v4 then 65507 else 65527) then return #[]
  if dst == 0 then return #[]
  let len := 8 + payload.size
  let datagram := be16 src.toNat ++ be16 dst.toNat ++ be16 len ++ be16 0 ++ payload
  let sum := checksum (Internet.pseudo (Internet.localIp cfg peer) peer.ip 17 len ++ datagram)
  let datagram := put16 datagram 6 (if sum == 0 then 65535 else sum)
  return ipFrames cfg peer 17 datagram id

end Kernel.Net.Fragment
