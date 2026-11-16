/-! # What a platform gives the service

The three things the demo service asks of whatever is underneath it. In the simulator they are a few lines of
C over a pipe and the operating system's random source (`rt/platform_hosted.c`); on bare metal they will be
the vsock driver and the enclave's random source. Nothing else in the service touches the outside. -/

namespace Platform

/-- Waits for bytes from the parent and returns at least one and at most `max` of them; empty once the
parent has closed the connection. -/
@[extern "silo_plat_read"]
opaque read (max : USize) : IO ByteArray

/-- Sends every byte to the parent. -/
@[extern "silo_plat_write"]
opaque write (bytes : @& ByteArray) : IO Unit

/-- `count` bytes from the platform's random source. -/
@[extern "silo_plat_random"]
opaque random (count : USize) : IO ByteArray

end Platform
