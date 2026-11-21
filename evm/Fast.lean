import Fast.Bytes
import Fast.Keccak
import Fast.Spike
import Fast.Word
import Fast.Wide
import Fast.State
import Fast.Machine
import Fast.Interp

/-! An execution engine written for speed, to take Jaune's place in what runs: the 256-bit word and its
arithmetic (`Word`, `Wide`), Keccak-256, the world as accounts and storage fetched when touched with a
journal to undo by (`State`), and the interpreter (`Machine`, `Interp`). `Spike` is the trial that settled
how the stack is held. Transactions and blocks are not written yet; `TODO.md` says where it stands. -/
