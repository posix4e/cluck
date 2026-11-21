import Evm.Machine

/-! The image for trying things on one machine: the same service (`Evm/Machine.lean`), which opens
connections only to the stand-in relay of `Evm.Relays.standIn`, a server on the host that anyone can be,
because its root's key is public (`scripts/standin.py`). It keeps nothing from the host and is not for
anything that matters: its measurement is its own, and is not the one of the image that is meant. -/

def main : IO UInt32 := Evm.Machine.run Evm.Relays.standIn
