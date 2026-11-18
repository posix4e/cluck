import Kernel.Net.Internet

/-! Static routing and neighbor resolution for locally initiated connections.
A route chooses a next-hop IP. Only the answer to a pending lookup can populate
the cache. A MAC address identifies a hop, not an authenticated remote peer. -/

namespace Kernel.Net.Route

open Internet

structure Table where
  ipv4Prefix : Nat := 24
  ipv4Gateway : Option ByteArray := some ⟨#[10,0,2,2]⟩
  ipv6Prefix : Nat := 64
  ipv6Gateway : Option ByteArray := some ⟨#[0xfe,0xc0,0,0,0,0,0,0,0,0,0,0,0,0,0,2]⟩

private def fitsPrefix (localIp dest : ByteArray) (bits : Nat) : Bool := Id.run do
  if localIp.size != dest.size || bits > localIp.size * 8 then return false
  let whole := bits / 8
  if localIp.extract 0 whole != dest.extract 0 whole then return false
  let rest := bits % 8
  if rest == 0 then return true
  let shift := (8 - rest).toUInt8
  return (localIp[whole]! >>> shift) == (dest[whole]! >>> shift)

/-- IP address whose Ethernet address must be resolved to deliver to dest. -/
def Table.nextHop (table : Table) (cfg : Config) (dest : ByteArray) : Option ByteArray := do
  let v4 := dest.size == 4
  guard (v4 || dest.size == 16)
  let prefixLen := if v4 then table.ipv4Prefix else table.ipv6Prefix
  guard (prefixLen ≤ dest.size * 8)
  let localIp := if v4 then cfg.ipv4 else cfg.ipv6
  if !v4 && dest[0]! == 0xfe && dest[1]! &&& 0xc0 == 0x80 then return dest
  if fitsPrefix localIp dest prefixLen then return dest
  let gw ← if v4 then table.ipv4Gateway else table.ipv6Gateway
  guard (gw.size == dest.size)
  return gw

private structure Entry where
  ip : ByteArray
  mac : Option ByteArray
  expires : Nat

structure Neighbors where
  private entries : Array Entry := #[]

inductive Lookup where
  | ready (peer : Peer)
  | solicit (frame : ByteArray)
  | pending
  | unreachable

/-- Resolve on demand. The caller retains its datagram and retries after a
neighbor event or timeout. Pending lookups expire after one second. -/
def Neighbors.lookup (ns : Neighbors) (now : Nat) (table : Table) (cfg : Config)
    (dest : ByteArray) : Neighbors × Lookup := Id.run do
  let live := ns.entries.filter (·.expires > now)
  let ns := { entries := live : Neighbors }
  let some ip := table.nextHop cfg dest | return (ns, .unreachable)
  if let some entry := live.find? (·.ip == ip) then
    let some mac := entry.mac | return (ns, .pending)
    return (ns, .ready { mac, ip := dest })
  let some frame := Internet.solicit cfg ip | return (ns, .unreachable)
  if live.size ≥ 32 then return (ns, .unreachable)
  return ({ entries := live.push { ip, mac := none, expires := now + 1000 } }, .solicit frame)

/-- An unsolicited advertisement cannot evict an established or unrelated mapping. -/
def Neighbors.learn (ns : Neighbors) (now : Nat) (peer : Peer) : Neighbors :=
  { entries := ns.entries.map fun e =>
    if now < e.expires && e.mac.isNone && e.ip == peer.ip then
      { e with mac := some peer.mac, expires := now + 30000 }
    else e }

end Kernel.Net.Route
