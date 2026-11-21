import Evm.Machine

/-! The image that is meant: the service as a whole machine (`Evm/Machine.lean`), which opens connections
only to the four relays of `Evm.Relays.live` and believes only the roots listed there about who they are. -/

def main : IO UInt32 := Evm.Machine.run Evm.Relays.live
