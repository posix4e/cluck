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

end Kernel.Efi
