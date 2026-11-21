import Fast.Bytes
import Fast.Keccak
import Fast.Spike
import Fast.Word
import Fast.Wide
import Fast.State
import Fast.Machine
import Fast.Interp
import Fast.Tx
import Fast.Block
import Fast.Bn254

/-! An execution engine written for speed, to take Jaune's place in what runs: the 256-bit word and its
arithmetic (`Word`, `Wide`), Keccak-256, the world as accounts and storage fetched when touched with a
journal to undo by (`State`), and the interpreter (`Machine`, `Interp`). `Spike` is the trial that settled
how the stack is held. `Tx` and `Block` are a transaction and a block on it. Nothing here imports Jaune;
`Evm/Bridge.lean` is where the two meet, and `TODO.md` says where the engine stands. -/
