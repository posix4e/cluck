import Evm.Roots
import Tls.X509

/-! Whom an image may talk to, and whom it believes about who they are.

The guest opens connections to relays itself, over TLS. Which relays, and which roots vouch for them, are
written here and so are part of what an image's measurement covers: the host can keep the guest from
reaching a relay, but cannot have it talk to anyone else in a relay's place, or name a root of its own.

There are two lists and two images. `live` is the four relays the builder sends to, under the roots their
certificates lead to (Let's Encrypt's and Google's). `standIn` is for testing on one machine: a single
name, `relay.test`, at the address the host has from inside QEMU's network, under a root whose key is
printed in `scripts/standin.py`. Anyone can be `relay.test`, so the image built with that list
(`EfiShadow.lean`) keeps nothing from anyone, and is a different image with a different measurement from
the one built with `live` (`EfiMain.lean`). -/

namespace Evm.Relays

structure Relay where
  /-- The name its certificate must be for, and the name looked up unless an address is given. -/
  name : String
  port : UInt16 := 443
  /-- Where it is, when it is not to be looked up by name. -/
  address : Option ByteArray := none

structure Table where
  relays : Array Relay
  /-- The roots' certificates. -/
  roots : Array ByteArray
  /-- What this list is, for the line the machine prints when it starts. -/
  what : String

def live : Table :=
  { relays := #[{ name := "boost-relay.flashbots.net" }, { name := "relay-builders-us.ultrasound.money" },
                { name := "aestus.live" }, { name := "us-global.titanrelay.xyz" }]
    roots := #[Roots.isrgX1, Roots.isrgX2, Roots.gtsR1, Roots.gtsR4]
    what := "four relays" }

def standIn : Table :=
  { relays := #[{ name := "relay.test", port := 5443, address := some ⟨#[10, 0, 2, 2]⟩ }]
    roots := #[Roots.standIn]
    what := "the stand-in relay, whose key everyone knows" }

/-- The roots as the certificate checker takes them. One that cannot be read is left out, and
`tls-test` checks that none is. -/
def Table.anchors (t : Table) : Array Tls.X509.Anchor := t.roots.filterMap (Tls.X509.Anchor.of ·)

/-- The earliest time a certificate is judged at: the day the roots were written down. A time before that
is somebody's mistake or somebody's attempt to have a certificate that has run out believed. -/
def earliest : Nat := Roots.written

end Evm.Relays
