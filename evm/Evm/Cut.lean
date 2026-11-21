import Evm.Stateless

/-! A witness cut from a whole state, for tests: every node of the state trie and of every storage trie,
every contract's code, every address and slot number. A test that has the whole state (a fixture's, or a
chain imported the ordinary way) uses this to put the same block to the stateless service. Nothing that
serves requests uses it. -/
open Jaune

namespace Evm.Cut

def headerBytes (h : Header) : ByteArray := (Header.toRlpItem h).toBytes.toByteArray

structure Witness where
  nodes : Array ByteArray
  codes : List ByteArray
  keys : List ByteArray
  root : U256

/-- A witness for all of a state. -/
def witnessOf (state : State) : Except Trie.Fault Witness := do
  let mut trie : Trie.Node := .empty
  let mut nodes : Array ByteArray := #[]
  let mut codes : List ByteArray := []
  let mut keys : List ByteArray := []
  for (address, account) in state.toList do
    let mut storage : Trie.Node := .empty
    for (slot, value) in Std.TreeMap.toList account.storage do
      storage ← Trie.put .empty storage (Stateless.keyOf slot.toBytes) (Stateless.slotValue value)
      keys := slot.toBytes.toByteArray :: keys
    nodes := Trie.encodings storage nodes
    let leaf : Stateless.Leaf :=
      ⟨account.nonce, account.balance, Trie.rootHash storage, Trie.hashOf account.code⟩
    trie ← Trie.put .empty trie (Stateless.keyOf address.toBytes) leaf.write
    if account.code.size > 0 then codes := account.code :: codes
    keys := address.toBytes.toByteArray :: keys
  pure ⟨Trie.encodings trie nodes, codes, keys, Trie.rootHash trie⟩

end Evm.Cut
