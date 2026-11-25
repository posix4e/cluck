import Evm.Machine

/-! The image with every engine in it: the same machine (`Evm/Machine.lean`) answering also what the
image that is meant refuses, which is everything Jaune does itself: a chain imported whole
(`Evm.Service`), a block and its witness judged by Jaune (`Evm.Stateless`), a block built by Jaune. It is
for putting the fixtures to a guest and for the page that shows one answering them (`demo/server.py`). It
opens connections only to the stand-in relay, like `EfiShadow.lean`, and its measurement is its own. -/

def main : IO UInt32 :=
  Evm.Machine.run Evm.Relays.standIn
    { other := Evm.Build.byJaune, rest := Evm.serve, what := "has every engine: Jaune's, and the fast one" }
