import Platform

/-! Raw frame and machine operations supplied by the UEFI target. All packet
interpretation happens above this interface. The hosted target reports that
firmware services are unavailable. -/

namespace Kernel.Efi

@[extern "silo_efi_mac"]
opaque mac : IO ByteArray

/-- An empty result means the device currently has no frame ready. -/
@[extern "silo_efi_receive"]
opaque receive : IO ByteArray

@[extern "silo_efi_send"]
opaque send (frame : @& ByteArray) : IO Unit

@[extern "silo_efi_millis"]
opaque millis : IO UInt64

@[extern "silo_efi_idle"]
opaque idle : IO Unit

/-- Exactly 64 bytes of caller-supplied REPORTDATA. The result is a local
TDREPORT, or empty when the platform cannot produce one. -/
@[extern "silo_efi_report"]
opaque report (data : @& ByteArray) : IO ByteArray

/-- The host asked to make a quote of what lies at `address`, `size` bytes of whole pages inside the
memory shared with the claimed device (`Kernel/Hw.lean`), and to put its answer there
(`Kernel/Quote.lean` fills it and reads it). 0 when the host took the request; anything else when it
did not, or when this is no trust domain. Stops the machine if the run is not inside that memory. -/
@[extern "silo_efi_quote_ask"]
opaque quoteAsk (address : UInt64) (size : UInt64) : BaseIO UInt64

end Kernel.Efi
