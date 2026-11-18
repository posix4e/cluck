import Kernel.Net.Route
import Kernel.Net.Fragment

open Kernel.Net Internet

private def check (condition : Bool) (what : String) : IO Unit :=
  unless condition do throw (IO.userError what)

private def guest : Config := { mac := ⟨#[2,0,0,0,0,1]⟩ }
private def remote : Config := {
  mac := ⟨#[2,0,0,0,0,2]⟩
  ipv4 := ⟨#[10,0,2,2]⟩
  ipv6 := ⟨#[0xfe,0xc0,0,0,0,0,0,0,0,0,0,0,0,0,0,2]⟩ }

private def routes : IO Unit := do
  let table : Route.Table := {}
  let dest := ByteArray.mk #[192,0,2,2]
  check (table.nextHop guest dest == some remote.ipv4) "IPv4 default gateway"
  check (table.nextHop guest (ByteArray.mk #[10,0,2,40]) == some ⟨#[10,0,2,40]⟩) "on-link IPv4"
  let partialPrefix := { table with ipv4Prefix := 25, ipv4Gateway := none }
  check ((partialPrefix.nextHop guest ⟨#[10,0,2,128]⟩).isNone) "non-byte-aligned subnet"
  check (table.nextHop guest remote.ipv6 == some remote.ipv6) "on-link IPv6"
  let ns : Route.Neighbors := {}
  let (ns, state) := ns.lookup 0 table guest dest
  let .solicit frame := state | throw (IO.userError "gateway lookup did not send ARP")
  check (frame.extract 38 42 == remote.ipv4) "must ARP for router, not remote destination"
  let (ns, state) := ns.lookup 1 table guest dest
  let .pending := state | throw (IO.userError "duplicate solicitation")
  let ns := ns.learn 2 { mac := guest.mac, ip := dest }
  let (_, state) := ns.lookup 3 table guest dest
  let .pending := state | throw (IO.userError "accepted unsolicited reply")
  let ns := ns.learn 4 { mac := remote.mac, ip := remote.ipv4 }
  let (_, .ready peer) := ns.lookup 5 table guest dest | throw (IO.userError "router unresolved")
  check (peer.ip == dest && peer.mac == remote.mac) "use router MAC and final IP"
  let (_, .solicit _) := ns.lookup 30004 table guest dest | throw (IO.userError "stale resolution")

private def fragments (v4 : Bool) : IO Unit := do
  let ip := if v4 then guest.ipv4 else guest.ipv6
  let src := if v4 then remote.ipv4 else remote.ipv6
  let peer := { ip, mac := guest.mac : Peer }
  let payload := ByteArray.mk ((Array.range 5000).map (fun n => (n % 251).toUInt8))
  let frames := Fragment.udpFrames remote peer 3210 5005 payload 0x23232323
  check (frames.size == 4 && frames.all (·.size ≤ 1514)) "Ethernet fragmentation"
  let mut cache : Fragment.Cache := {}
  for i in #[3, 0, 2] do
    let (next, result) := cache.receive 0 guest frames[i]!
    check result.isNone "delivered incomplete IP datagram"
    cache := next
  let (done_, result) := cache.receive 1 guest frames[1]!
  let some (.udp sender 3210 5005 data) := result | throw (IO.userError "UDP reassembly failed")
  check (data == payload && sender.ip == src) "reassembled incorrect payload"
  let (_, again_) := done_.receive 2 guest frames[1]!
  check again_.isNone "reused completed assembly"
  let (poisoned, _) := cache.receive 2 guest frames[0]!
  let (_, overlap) := poisoned.receive 3 guest frames[1]!
  check overlap.isNone "accepted overlapping fragments"
  let (_, expired) := cache.receive 60000 guest frames[1]!
  check expired.isNone "completed expired reassembly"

def main : IO Unit := do
  routes
  fragments true
  fragments false
  IO.println "net-route-test: routes, cache lifetimes, and IPv4/IPv6 reassembly passed"
