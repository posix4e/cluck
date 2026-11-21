import Jaune.Transaction
import Fast.Keccak

/-! # A Merkle-Patricia trie that can be known in part

Jaune computes a state root by hashing every account (`State.root`). That needs the whole state. A block of
the real chain touches a few thousand accounts out of hundreds of millions, and what can be sent with it is
a witness: the trie nodes on the paths to what the block touches, each named by its hash.

This file is a trie whose nodes are either known or `sealed`: known only by hash. A sealed node is opened by
finding its bytes in the witness, and reading or changing a key opens only the nodes on its path. So a
lookup has three answers, not two: the value, proof that there is none, or `missing` when the path runs into
a node the witness does not hold. Nothing is ever assumed about a node that was not supplied.

Keys are paths of nibbles, all of one length in a given trie (64 for the state and storage tries, whose keys
are hashes). Values are opaque bytes, already encoded as the trie stores them. Node encodings are read
strictly: canonical RLP only, a branch holds no value, a child is an empty string, a 32-byte hash or an
embedded node shorter than 32 bytes, and a path has at most 64 nibbles. -/

open Jaune

namespace Evm.Trie

/-- A path of nibbles, each below 16. -/
abbrev Path := Array UInt8

inductive Node where
  | empty
  | leaf (path : Path) (value : ByteArray)
  | ext (path : Path) (child : Node)
  /-- Exactly sixteen children. -/
  | branch (children : Array Node)
  /-- A node known only by the hash of its encoding. -/
  | sealed (hash : U256)
  deriving Inhabited

inductive Fault where
  /-- The witness does not hold the node with this hash. -/
  | missing (hash : U256)
  /-- The witness holds bytes with this hash, and they are not a node. -/
  | malformed (hash : U256)
  /-- A key that is a prefix of another, or longer than the trie is deep: not a trie of equal-length keys. -/
  | shape

def hashOf (bytes : ByteArray) : U256 :=
  let d := Fast.Keccak.hash bytes 0 bytes.size
  ⟨⟨Fast.swap d.w0, Fast.swap d.w1⟩, ⟨Fast.swap d.w2, Fast.swap d.w3⟩⟩

/-- The 32 bytes of a word, highest first. Written from its four 64-bit parts, with no list between. -/
def wordBytes (w : U256) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for part in [w.1.1, w.1.2, w.2.1, w.2.2] do
    for k in [0 : 8] do
      out := out.push (part >>> (56 - 8 * k).toUInt64).toUInt8
  return out

/-- Words in the order of their bytes. A map of hashes is looked into for every node of a witness, and
Jaune's own `compare` on words goes through two generic comparisons of pairs of pairs. -/
def order (a b : U256) : Ordering :=
  (compare a.1.1 b.1.1).then <| (compare a.1.2 b.1.2).then <| (compare a.2.1 b.2.1).then (compare a.2.2 b.2.2)

/-- The nibbles of some bytes, high half first. -/
def nibbles (bytes : ByteArray) : Path :=
  bytes.foldl (fun out b => (out.push (b >>> 4)).push (b &&& 0x0f)) (Array.mkEmpty (2 * bytes.size))

/-! ## Writing a node -/

def rlpLength (base : UInt8) (n : Nat) : ByteArray :=
  if n ≤ 55 then ⟨#[base + n.toUInt8]⟩
  else
    let digits := ((List.range 4).reverse.map fun k => (n >>> (8 * k)).toUInt8).dropWhile (· == 0)
    ⟨#[base + 55 + digits.length.toUInt8]⟩ ++ digits.toByteArray

def rlpString (s : ByteArray) : ByteArray :=
  if s.size == 1 && s[0]! < 0x80 then s else rlpLength 0x80 s.size ++ s

def rlpList (payload : ByteArray) : ByteArray := rlpLength 0xc0 payload.size ++ payload

/-- A path as a node holds it: a flag nibble for leaf or extension and odd or even, then the nibbles. -/
def hexPrefix (path : Path) (leaf : Bool) : ByteArray := Id.run do
  let flag : UInt8 := if leaf then 2 else 0
  let odd := path.size % 2 == 1
  let mut out : ByteArray := ⟨#[if odd then ((flag + 1) <<< 4) ||| path[0]! else flag <<< 4]⟩
  let mut i := if odd then 1 else 0
  while i + 1 < path.size do
    out := out.push ((path[i]! <<< 4) ||| path[i + 1]!)
    i := i + 2
  return out

mutual
  /-- A node's own encoding. A sealed node has none here; `reference` is what stands for it. -/
  partial def encode : Node → ByteArray
    | .empty => ⟨#[0x80]⟩
    | .leaf path value => rlpList (rlpString (hexPrefix path true) ++ rlpString value)
    | .ext path child => rlpList (rlpString (hexPrefix path false) ++ reference child)
    | .branch children =>
      rlpList (children.foldl (fun out child => out ++ reference child) .empty ++ ⟨#[0x80]⟩)
    | .sealed hash => rlpString (wordBytes hash)

  /-- What a parent holds for a child: nothing, the child itself if it is short, or its hash. -/
  partial def reference : Node → ByteArray
    | .empty => ⟨#[0x80]⟩
    | .sealed hash => rlpString (wordBytes hash)
    | node =>
      let bytes := encode node
      if bytes.size < 32 then bytes else rlpString (wordBytes (hashOf bytes))
end

/-- The root hash of a trie. The root is always named by hash, however short it is. -/
def rootHash : Node → U256
  | .sealed hash => hash
  | node => hashOf (encode node)

/-! ## Reading a node -/

private structure Item where
  list : Bool
  start : Nat
  size : Nat
  deriving Inhabited

private def Item.stop (i : Item) : Nat := i.start + i.size

private def longLength (b : ByteArray) (pos count : Nat) : Option Nat :=
  if count == 0 || count > 4 || pos + count > b.size || b[pos]! == 0 then none
  else
    let n := (List.range count).foldl (fun acc k => acc * 256 + b[pos + k]!.toNat) 0
    if n ≤ 55 then none else some n

/-- The RLP item whose first byte is at `pos`, in canonical form only. -/
private def item (b : ByteArray) (pos : Nat) : Option Item := do
  guard (pos < b.size)
  let first := b[pos]!.toNat
  let it : Item ←
    if first < 0x80 then pure ⟨false, pos, 1⟩
    else if first ≤ 0xb7 then
      let n := first - 0x80
      if n == 1 && pos + 1 < b.size && b[pos + 1]! < 0x80 then none else pure ⟨false, pos + 1, n⟩
    else if first ≤ 0xbf then
      let count := first - 0xb7
      pure ⟨false, pos + 1 + count, ← longLength b (pos + 1) count⟩
    else if first ≤ 0xf7 then pure ⟨true, pos + 1, first - 0xc0⟩
    else
      let count := first - 0xf7
      pure ⟨true, pos + 1 + count, ← longLength b (pos + 1) count⟩
  guard (it.stop ≤ b.size)
  pure it

/-- The items from `pos` to `stop`, each with where its own first byte is; no more than seventeen. -/
private partial def items (b : ByteArray) (pos stop : Nat) (out : Array (Nat × Item)) :
    Option (Array (Nat × Item)) :=
  if pos == stop then some out
  else if out.size == 17 then none
  else do
    let it ← item b pos
    guard (it.stop ≤ stop)
    items b it.stop stop (out.push (pos, it))

private def word64 (b : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for k in [0 : 8] do w := (w <<< 8) ||| b[i + k]!.toUInt64
  return w

/-- The 32 bytes from `start` as a word, highest first; zero if there are not 32. A branch reads up to
sixteen of these, and each used to be cut out, made a list and read from the list. -/
def word (b : ByteArray) (start : Nat) : U256 :=
  if start + 32 > b.size then 0
  else ⟨⟨word64 b start, word64 b (start + 8)⟩, ⟨word64 b (start + 16), word64 b (start + 24)⟩⟩

private def readPath (s : ByteArray) : Option (Path × Bool) := do
  guard (s.size ≥ 1 && s.size ≤ 33)
  let flag := s[0]! >>> 4
  guard (flag < 4)
  let odd := flag &&& 1 == 1
  guard (odd || s[0]! &&& 0x0f == 0)
  let rest := nibbles (s.extract 1 s.size)
  let path := if odd then #[s[0]! &&& 0x0f] ++ rest else rest
  guard (path.size ≤ 64)
  pure (path, flag ≥ 2)

/-- A node from its encoding, or `none` if the bytes are not exactly one well-formed node. -/
partial def decode (b : ByteArray) : Option Node := do
  let top ← item b 0
  guard (top.list && top.stop == b.size)
  let parts ← items b top.start top.stop #[]
  let child (part : Nat × Item) : Option Node :=
    let (head, it) := part
    if it.list then (if it.stop - head < 32 then decode (b.extract head it.stop) else none)
    else if it.size == 0 then some .empty
    else if it.size == 32 then some (.sealed (word b it.start))
    else none
  if parts.size == 17 then
    let last := parts[16]!.2
    guard (!last.list && last.size == 0)
    let children ← (parts.extract 0 16).mapM child
    -- A branch with fewer than two children is not one a trie would hold.
    guard (children.foldl (fun n c => if c matches .empty then n else n + 1) 0 ≥ 2)
    pure (.branch children)
  else if parts.size == 2 then
    let first := parts[0]!.2
    guard (!first.list)
    let (path, leaf) ← readPath (b.extract first.start first.stop)
    if leaf then
      let value := parts[1]!.2
      guard (!value.list && value.size > 0)
      pure (.leaf path (b.extract value.start value.stop))
    else
      guard (path.size > 0)
      let below ← child parts[1]!
      -- An extension leads to a branch; it never ends the trie and never leads to nothing.
      guard (!(below matches .empty))
      pure (.ext path below)
  else none

/-! ## The witness -/

/-- Node encodings by their hash. -/
abbrev Store := Std.TreeMap U256 ByteArray order

def Store.ofNodes (nodes : Array ByteArray) : Store :=
  nodes.foldl (fun store node => store.insert (hashOf node) node) .empty

/-- The root of a trie with nothing in it, which no witness holds a node for. -/
def emptyRoot : U256 := hashOf ⟨#[0x80]⟩

/-- The node itself: a sealed one is looked for in the witness. The result is never sealed. -/
def resolve (store : Store) : Node → Except Fault Node
  | .sealed hash =>
    if hash == emptyRoot then .ok .empty else
    match store.get? hash with
    | none => .error (.missing hash)
    | some bytes =>
      match decode bytes with
      | some node => .ok node
      | none => .error (.malformed hash)
  | node => .ok node

private def sharedFrom (a : Path) (b : Path) (from_ : Nat) : Nat := Id.run do
  let mut n := 0
  while n < a.size && from_ + n < b.size && a[n]! == b[from_ + n]! do n := n + 1
  return n

private def wrap (path : Path) (node : Node) : Node := if path.isEmpty then node else .ext path node

private def emptyBranch : Array Node := Array.replicate 16 .empty

/-- The value at `key`, read from nibble `i` on: `none` is proof there is none. -/
partial def get (store : Store) (node : Node) (key : Path) (i : Nat := 0) :
    Except Fault (Option ByteArray) := do
  match ← resolve store node with
  | .empty => pure none
  | .leaf path value => pure (if path == key.extract i key.size then some value else none)
  | .ext path child =>
    if sharedFrom path key i == path.size then get store child key (i + path.size) else pure none
  | .branch children =>
    if i < key.size then get store children[key[i]!.toNat]! key (i + 1) else .error .shape
  | .sealed _ => .error .shape

/-- The trie with `value` at `key`. -/
partial def set (store : Store) (node : Node) (key : Path) (value : ByteArray) (i : Nat := 0) :
    Except Fault Node := do
  match ← resolve store node with
  | .empty => pure (.leaf (key.extract i key.size) value)
  | .leaf path old =>
    let n := sharedFrom path key i
    if n == path.size && i + n == key.size then pure (.leaf path value)
    else if n == path.size || i + n == key.size then .error .shape
    else
      let children := emptyBranch.set! path[n]!.toNat (.leaf (path.extract (n + 1) path.size) old)
      let children := children.set! key[i + n]!.toNat (.leaf (key.extract (i + n + 1) key.size) value)
      pure (wrap (path.extract 0 n) (.branch children))
  | .ext path child =>
    let n := sharedFrom path key i
    if n == path.size then pure (.ext path (← set store child key value (i + n)))
    else if i + n == key.size then .error .shape
    else
      let children := emptyBranch.set! path[n]!.toNat (wrap (path.extract (n + 1) path.size) child)
      let children := children.set! key[i + n]!.toNat (.leaf (key.extract (i + n + 1) key.size) value)
      pure (wrap (path.extract 0 n) (.branch children))
  | .branch children =>
    if i < key.size then
      let slot := key[i]!.toNat
      pure (.branch (children.set! slot (← set store children[slot]! key value (i + 1))))
    else .error .shape
  | .sealed _ => .error .shape

/-- What stands where a node was when `nibble` and then `node` is all that is left under it. To say which,
the node has to be known, which is where a witness can fall short. -/
private def absorb (store : Store) (path : Path) (node : Node) : Except Fault Node := do
  match ← resolve store node with
  | .leaf rest value => pure (.leaf (path ++ rest) value)
  | .ext rest child => pure (.ext (path ++ rest) child)
  | .empty => pure .empty
  -- A branch stays as it was given, sealed if it was sealed, so its hash is not computed again.
  | _ => pure (.ext path node)

/-- The trie without `key`, which must be in it (`remove` checks). -/
private partial def delete (store : Store) (node : Node) (key : Path) (i : Nat) : Except Fault Node := do
  match ← resolve store node with
  | .leaf _ _ => pure .empty
  | .ext path child => absorb store path (← delete store child key (i + path.size))
  | .branch children =>
    let slot := key[i]!.toNat
    let children := children.set! slot (← delete store children[slot]! key (i + 1))
    let left := (List.range 16).filter fun j => !(children[j]! matches .empty)
    match left with
    | [only] => absorb store #[only.toUInt8] children[only]!
    | _ => pure (.branch children)
  | _ => .error .shape

/-- The trie without `key`. A key that is not there leaves the trie as it was, sealed nodes and all. -/
def remove (store : Store) (node : Node) (key : Path) : Except Fault Node := do
  match ← get store node key with
  | none => pure node
  | some _ => delete store node key 0

/-- The trie with `value` at `key`; an empty value removes the key. A value already there leaves the trie
as it was. -/
def put (store : Store) (node : Node) (key : Path) (value : ByteArray) : Except Fault Node := do
  if value.isEmpty then remove store node key
  else if (← get store node key) == some value then pure node
  else set store node key value

/-- Every key and value that can be reached from `node` through the witness, with `path` in front of each
key. A subtree the witness does not hold is passed over: what is under it is unknown, not absent, and
`get` says so when asked for a key there. -/
partial def leaves (store : Store) (node : Node) (path : Path := #[])
    (out : Array (Path × ByteArray) := #[]) : Except Fault (Array (Path × ByteArray)) := do
  if path.size > 64 then .error .shape
  match resolve store node with
  | .error (.missing _) => pure out
  | .error fault => .error fault
  | .ok .empty => pure out
  | .ok (.leaf rest value) => pure (out.push (path ++ rest, value))
  | .ok (.ext rest child) => leaves store child (path ++ rest) out
  | .ok (.branch children) =>
    let mut out := out
    for slot in [0 : 16] do
      out ← leaves store children[slot]! (path.push slot.toUInt8) out
    pure out
  | .ok (.sealed _) => .error .shape

/-- The strings of an RLP list that holds nothing but strings, such as an account, or `none`. -/
def strings (b : ByteArray) : Option (Array ByteArray) := do
  let top ← item b 0
  guard (top.list && top.stop == b.size)
  (← items b top.start top.stop #[]).mapM fun (_, it) =>
    if it.list then none else some (b.extract it.start it.stop)

/-- The string that is the whole of `b` as RLP, or `none`. -/
def string (b : ByteArray) : Option ByteArray := do
  let top ← item b 0
  guard (!top.list && top.stop == b.size)
  pure (b.extract top.start top.stop)

/-- The word a path of 64 nibbles spells: the hash a state or storage key is. Zero for any other path. -/
def pathWord (path : Path) : U256 :=
  if path.size != 64 then 0 else
  let part (i : Nat) : UInt64 := Id.run do
    let mut w : UInt64 := 0
    for k in [0 : 16] do w := (w <<< 4) ||| path[i + k]!.toUInt64
    return w
  ⟨⟨part 0, part 16⟩, ⟨part 32, part 48⟩⟩

/-- The encoding of every node of a trie that a parent names by hash, and of the root: a witness for all
of it. Sealed nodes are not opened. -/
partial def encodings (node : Node) (out : Array ByteArray := #[]) (root : Bool := true) : Array ByteArray :=
  let out :=
    match node with
    | .empty | .sealed _ => out
    | _ =>
      let bytes := encode node
      if root || bytes.size ≥ 32 then out.push bytes else out
  match node with
  | .ext _ child => encodings child out false
  | .branch children => children.foldl (fun out child => encodings child out false) out
  | _ => out

end Evm.Trie
