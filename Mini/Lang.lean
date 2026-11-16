/-! # A small language for the code under Lean

The allocator, reference counts and object layout are what compiled Lean stands on, so they cannot be written
in Lean as it is compiled. They can be written as *data* in Lean: programs in a language small enough to say
exactly what each step does, from which the C is printed (`Mini/Print.lean`). What is reasoned about and what
is compiled are then the same text.

The language has one type, the 64-bit word. A program has global words, global arrays of words, and
functions from words to a word. Memory is read and written a word at a time at an address that is itself a
word. There is no pointer type to get wrong and nothing is implicit: no conversions, no overflow that is not
wrap-around, no evaluation order to choose (calls are statements, so an expression has no effects). -/

namespace Mini

inductive Op
  | add | sub | mul | div | shl | shr | and | or
  /-- Comparisons of words as unsigned numbers: 1 if it holds, 0 if not. -/
  | eq | ne | lt | le
  deriving Repr, DecidableEq

inductive Expr
  | lit (value : UInt64)
  /-- A parameter or a local. -/
  | var (name : String)
  | global (name : String)
  /-- Element `i` of a global array. The printed C checks nothing: staying inside is the program's to show. -/
  | item (array : String) (i : Expr)
  /-- The word in memory at an address. -/
  | load (address : Expr)
  | op (o : Op) (a b : Expr)
  deriving Repr

inductive Stmt
  | set (name : String) (value : Expr)
  | setGlobal (name : String) (value : Expr)
  | setItem (array : String) (i value : Expr)
  | store (address value : Expr)
  | branch (condition : Expr) (yes no : List Stmt)
  | loop (condition : Expr) (body : List Stmt)
  /-- A call of one of the program's own functions. -/
  | call (result : Option String) (function : String) (arguments : List Expr)
  /-- A call out of the program, as the C to write. What it does is an assumption wherever it is used. -/
  | outside (result : Option String) (c : String)
  /-- Stop the machine, saying why. Nothing after it runs. -/
  | stop (why : String)
  | give (value : Expr)
  deriving Repr

/-- How a function is seen from C, if it is: the C types of its result and of its parameters. -/
structure Seen where
  result : String
  parameters : List String
  deriving Repr

structure Function where
  name : String
  parameters : List String
  body : List Stmt
  seen : Option Seen := none
  about : String := ""
  deriving Repr

structure Program where
  about : String
  /-- What the printed file has to declare first: includes, and the functions called from `outside`. -/
  preamble : String
  globals : List String
  arrays : List (String × Nat)
  functions : List Function
  deriving Repr

/-! Writing programs down. -/

instance : OfNat Expr n := ⟨.lit (UInt64.ofNat n)⟩
instance : Add Expr := ⟨.op .add⟩
instance : Sub Expr := ⟨.op .sub⟩
instance : Mul Expr := ⟨.op .mul⟩
instance : Div Expr := ⟨.op .div⟩
instance : Coe String Expr := ⟨.var⟩

def Expr.shl (a b : Expr) : Expr := .op .shl a b
def Expr.shr (a b : Expr) : Expr := .op .shr a b
def Expr.and (a b : Expr) : Expr := .op .and a b
def Expr.or (a b : Expr) : Expr := .op .or a b
def Expr.eq (a b : Expr) : Expr := .op .eq a b
def Expr.ne (a b : Expr) : Expr := .op .ne a b
def Expr.lt (a b : Expr) : Expr := .op .lt a b
def Expr.le (a b : Expr) : Expr := .op .le a b

end Mini
