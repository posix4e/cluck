namespace Kernel.Net.Internet

structure Config where
  mac : ByteArray
  ipv4 : ByteArray := ⟨#[10, 0, 2, 15]⟩
  ipv6 : ByteArray := ⟨#[0xfe, 0xc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x15]⟩

/-- The peer's IP and the next hop that delivered its packet. For a routed peer the latter is the router. -/
structure Peer where
  mac : ByteArray
  ip : ByteArray
  deriving BEq, Inhabited

end Kernel.Net.Internet
