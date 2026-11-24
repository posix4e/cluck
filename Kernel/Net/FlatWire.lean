import Kernel.Net.Flat

/-! What a guest that serves the trial TCP (`Kernel/Net/Flat.lean`) from a network card needs besides the
TCP, whichever card it is: an answer to whoever asks for its Ethernet address, and a count of the SYNs in
a batch, for deciding whether to take new connections. -/

namespace Kernel.Net.FlatWire

open Kernel.Net.Flat

/-- For every frame of `rx` that asks whose Ethernet address `cfg.localIp` is, the answer written to `tx`
after what is there. -/
partial def neighbours (cfg : @& Tuning) (rx : @& ByteArray) (o stop : USize) (tx : ByteArray) : ByteArray :=
  if o + 2 > stop then tx else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  if f + n > stop then tx else
  if n ≥ 42 && rd16 rx (f + 12) == 0x0806 && rd16 rx (f + 20) == 1 && rd32 rx (f + 38) == cfg.localIp then
    let at_ := written tx
    if at_.toNat + 62 > tx.size then tx else
    let e := at_ + 2
    let tx := wr16 tx at_ 60
    -- To the asker, from here; then the same question's fields turned round.
    let tx := wr32 (wr16 tx e (rd16 rx (f + 6))) (e + 2) (rd32 rx (f + 8))
    let tx := wr32 (wr16 tx (e + 6) cfg.macHigh) (e + 8) cfg.macLow
    let tx := wr16 tx (e + 12) 0x0806
    let tx := wr32 (wr32 tx (e + 14) 0x00010800) (e + 18) 0x06040002
    let tx := wr32 (wr16 tx (e + 22) cfg.macHigh) (e + 24) cfg.macLow
    let tx := wr32 tx (e + 28) cfg.localIp
    let tx := wr32 (wr16 tx (e + 32) (rd16 rx (f + 22))) (e + 34) (rd32 rx (f + 24))
    let tx := wr32 tx (e + 38) (rd32 rx (f + 28))
    -- The rest of the sixty bytes is nothing, and must be written so: the array is used again and again.
    let tx := wr32 (wr32 (wr32 (wr32 (wr16 tx (e + 42) 0) (e + 44) 0) (e + 48) 0) (e + 52) 0) (e + 56) 0
    neighbours cfg rx (f + n) stop (st64 tx 0 (at_ + 62).toUInt64)
  else neighbours cfg rx (f + n) stop tx

/-- How many of the frames in `rx` from `o` to `stop` look like SYNs: long enough, and with that flag and
not the acknowledging one where a TCP header's flags would be. Near enough for deciding whether to take
new connections; the TCP itself looks properly. -/
partial def synsIn (rx : @& ByteArray) (o stop : USize) (found : UInt64) : UInt64 :=
  if o + 2 > stop then found else
  let n := (rd16 rx o).toUSize
  synsIn rx (o + 2 + n) stop (if n ≥ 54 && rd8 rx (o + 2 + 47) &&& 0x12 == 0x02 then found + 1 else found)

end Kernel.Net.FlatWire
