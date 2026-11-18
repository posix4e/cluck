import Kernel.Net.Route

/-! A DNS stub resolver for A and AAAA records over UDP. Feed one lookup raw Internet events
and the monotonic time. It emits ARP/ND and UDP frames, retries after a second, and gives up
after five seconds. The requesting service supplies the resolver IP and independently randomizes
the transaction ID and an unused ephemeral UDP port. -/

namespace Kernel.Net.Dns

open Internet

inductive Kind where
  | a | aaaa
  deriving BEq

private def Kind.code (kind : Kind) : Nat := if kind == .a then 1 else 28

inductive Answer where
  | addresses (ips : Array ByteArray)
  | noData
  | serverError (rcode : UInt8)
  | truncated
  | timeout
  | unreachable
  deriving BEq

inductive Action where
  | wait
  | transmit (frame : ByteArray)
  | done (answer : Answer)

private def be16 (n : Nat) : ByteArray := ⟨#[(n / 256).toUInt8, n.toUInt8]⟩
private def get16 (b : ByteArray) (i : Nat) : Nat := 256 * b[i]!.toNat + b[i+1]!.toNat
private def lower (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- Keep the labels length-delimited after case folding. A dot in a wire label therefore cannot
match a label boundary in the name the caller asked for. -/
private def hostname (name : String) : Option ByteArray := do
  guard (name.utf8ByteSize > 0 && name.utf8ByteSize ≤ 254)
  let bytes := name.toUTF8
  let length := if bytes[bytes.size-1]! == 46 then bytes.size-1 else bytes.size
  guard (length > 0)
  let mut out := ByteArray.empty
  let mut label := ByteArray.empty
  for i in [:length] do
    let b := lower bytes[i]!
    if b == 46 then
      guard (!label.isEmpty)
      out := (out.push label.size.toUInt8) ++ label
      label := ByteArray.empty
    else
      guard (label.size < 63 && ((97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) || b == 45 || b == 95))
      label := label.push b
  guard (!label.isEmpty)
  out := ((out.push label.size.toUInt8) ++ label).push 0
  guard (out.size ≤ 255)
  return out

/-- Read one possibly compressed name and the offset where the next field starts. RFC 1035
pointers target earlier wire offsets. Fuel additionally bounds chains that alternate labels
and pointers and maliciously revisit the same offsets. -/
private def nameAt (b : ByteArray) (start : Nat) : Option (ByteArray × Nat) :=
  let rec read : Nat → Nat → Option Nat → ByteArray → Option (ByteArray × Nat)
    | 0, _, _, _ => none
    | fuel+1, pos, stop, name => do
      guard (pos < b.size)
      let len := b[pos]!.toNat
      if len == 0 then return (name.push 0, stop.getD (pos+1))
      if len ≥ 192 then
        guard (pos+1 < b.size)
        let target := (len % 64) * 256 + b[pos+1]!.toNat
        guard (target ≥ 12 && target < pos)
        read fuel target (some (stop.getD (pos+2))) name
      else
        guard (len ≤ 63 && pos + 1 + len ≤ b.size && name.size + 1 + len ≤ 254)
        let mut out := name.push len.toUInt8
        for i in [:len] do out := out.push (lower b[pos+1+i]!)
        read fuel (pos + 1 + len) stop out
  read 144 start none ByteArray.empty

private structure Record where
  owner : ByteArray
  typ : Nat
  val : ByteArray

private def record (b : ByteArray) (pos : Nat) (keep : Bool) : Option (Option Record × Nat) := do
  let (owner, i) ← nameAt b pos
  guard (i + 10 ≤ b.size)
  let typ := get16 b i
  let first := i + 10
  let last := first + get16 b (i+8)
  guard (last ≤ b.size)
  if !keep || get16 b (i+2) != 1 then return (none, last)
  if typ == 5 then
    let (cname, consumed) ← nameAt b first
    guard (consumed == last)
    return (some { owner, typ, val := cname }, last)
  if typ != 1 && typ != 28 then return (none, last)
  guard (last - first == (if typ == 1 then 4 else 16))
  return (some { owner, typ, val := b.extract first last }, last)

private def answerFor (records : Array Record) (name : ByteArray) (kind : Kind) : Option Answer := do
  let mut owner := name
  let mut visited : Array ByteArray := #[]
  for _ in [:9] do
    guard (!visited.contains owner)
    visited := visited.push owner
    let matching := records.filter (·.owner == owner)
    let ips := (matching.filter (·.typ == kind.code)).map (·.val)
    let aliases := matching.filter (·.typ == 5)
    if aliases.isEmpty then return if ips.isEmpty then .noData else .addresses ips
    guard (ips.isEmpty && aliases.size == 1)
    let alias ← aliases[0]?
    owner := alias.val
  none

structure Query where
  private server : ByteArray
  private port : UInt16
  private id : UInt16
  private name : ByteArray
  private kind : Kind
  private question : ByteArray
  private deadline : Nat
  private nextSend : Nat
  private sent : Bool := false
  private answer : Option Answer := none
  private neighbors : Route.Neighbors := {}

def Query.start (now : Nat) (server : ByteArray) (localPort id : UInt16) (name : String)
    (kind : Kind) : Option Query := do
  guard ((server.size == 4 || server.size == 16) && localPort ≥ 49152)
  let name ← hostname name
  let question := be16 id.toNat ++ (ByteArray.mk #[1,0,0,1,0,0,0,0,0,0]) ++
    name ++ be16 kind.code ++ be16 1
  return { server, port := localPort, id, name, kind, question, deadline := now + 5000, nextSend := now }

private def Query.parse (q : Query) (msg : ByteArray) : Option Answer := do
  guard (msg.size ≥ 12 && msg.size ≤ 512 && get16 msg 0 == q.id.toNat && get16 msg 4 == 1)
  let flags := get16 msg 2
  guard (flags &&& 0xf840 == 0x8000)
  let (name, i) ← nameAt msg 12
  guard (name == q.name && i+4 ≤ msg.size && get16 msg i == q.kind.code && get16 msg (i+2) == 1)
  if flags &&& 0x0200 != 0 then return .truncated
  let count := get16 msg 6
  let total := count + get16 msg 8 + get16 msg 10
  guard (total ≤ 48)
  let mut pos := i+4
  let mut answers := #[]
  for k in [:total] do
    let (rr, next) ← record msg pos (k < count)
    if let some rr := rr then answers := answers.push rr
    pos := next
  guard (pos == msg.size)
  let rcode := (flags &&& 15).toUInt8
  if rcode != 0 then return .serverError rcode
  answerFor answers name q.kind

private def Query.finish (q : Query) (answer : Answer) : Query × Action :=
  ({ q with answer := some answer }, .done answer)

/-- Call on each Internet event and on timer ticks, passing the returned Query into the next call.
The resolver binds an answer to its server, UDP ports, transaction ID, question and record owner.
A truncated response is surfaced explicitly so the caller can select a TCP-capable resolver. -/
def Query.step (q : Query) (now : Nat) (cfg : Config) (routes : Route.Table)
    (input : Option Event) : Query × Action := Id.run do
  if let some answer := q.answer then return (q, .done answer)
  if now ≥ q.deadline then return q.finish .timeout
  let mut q := q
  match input with
  | some (.udp peer src dst msg) =>
    if q.sent && peer.ip == q.server && src == 53 && dst == q.port then
      if let some answer := q.parse msg then return q.finish answer
  | some (.neighbor peer) => q := { q with neighbors := q.neighbors.learn now peer }
  | _ => pure ()
  if now < q.nextSend then return (q, .wait)
  let (neighbors, lookup) := q.neighbors.lookup now routes cfg q.server
  q := { q with neighbors }
  match lookup with
  | .pending => return (q, .wait)
  | .unreachable => return q.finish .unreachable
  | .solicit frame => return (q, .transmit frame)
  | .ready peer =>
    let some frame := udpFrame cfg peer q.port 53 q.question | return q.finish .unreachable
    return ({ q with sent := true, nextSend := now + 1000 }, .transmit frame)

end Kernel.Net.Dns
