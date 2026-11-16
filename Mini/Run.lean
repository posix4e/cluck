import Mini.Lang
import Std.Data.HashMap

/-! # What a program means

Running a program, a step at a time, in Lean. This is the language's definition: the printed C is meant to
do what this does, wherever this does not fail.

It fails where C would leave the outcome open, so that a program shown never to fail here does not depend on
any of it: dividing by zero, shifting by 64 or more, reading or writing outside a global array, reading a
local that was never set, reading memory nothing has written, and an address that is not a multiple of
eight. Arithmetic wraps, as it does on the machine.

A call out of the program is whatever `outside` says it is. Running out of `fuel` is a failure too: a
function that needs more steps than it was given has not been shown to finish. -/

namespace Mini

structure State where
  globals : Std.HashMap String UInt64 := {}
  arrays : Std.HashMap String (Array UInt64) := {}
  memory : Std.HashMap UInt64 UInt64 := {}

/-- How a function or a run of statements ends. -/
inductive Ending
  | on
  | gave (value : UInt64)
  | stopped (why : String)

abbrev Locals := Std.HashMap String UInt64

/-- What a call out of the program does: given the C text, a result and the state after. -/
abbrev Outside := String → State → Except String (UInt64 × State)

def Op.run (o : Op) (a b : UInt64) : Except String UInt64 :=
  let truth (p : Bool) : UInt64 := if p then 1 else 0
  match o with
  | .add => pure (a + b) | .sub => pure (a - b) | .mul => pure (a * b)
  | .div => if b == 0 then throw "division by zero" else pure (a / b)
  | .shl => if b ≥ 64 then throw "a shift by 64 or more" else pure (a <<< b)
  | .shr => if b ≥ 64 then throw "a shift by 64 or more" else pure (a >>> b)
  | .and => pure (a &&& b) | .or => pure (a ||| b)
  | .eq => pure (truth (a == b)) | .ne => pure (truth (a != b))
  | .lt => pure (truth (a < b)) | .le => pure (truth (a ≤ b))

def Expr.run (s : State) (locals : Locals) : Expr → Except String UInt64
  | .lit value => pure value
  | .var name => match locals[name]? with
    | some value => pure value
    | none => throw s!"the local {name} is read before it is set"
  | .global name => pure (s.globals.getD name 0)
  | .item array i => do
    let i ← i.run s locals
    match s.arrays[array]? with
    | none => throw s!"no array {array}"
    | some items => if h : i.toNat < items.size then pure items[i.toNat] else throw s!"{array}[{i}] is outside it"
  | .load address => do
    let address ← address.run s locals
    if address % 8 != 0 then throw s!"a read at {address}, which is not a multiple of eight"
    match s.memory[address]? with
    | some word => pure word
    | none => throw s!"a read at {address}, which nothing has written"
  | .op o a b => do o.run (← a.run s locals) (← b.run s locals)

def bind (locals : Locals) : List String → List UInt64 → Locals
  | name :: names, value :: values => bind (locals.insert name value) names values
  | _, _ => locals

mutual
  def Stmt.run (p : Program) (outside : Outside) : Nat → Stmt → State → Locals → Except String (Ending × State × Locals)
    | 0, _, _, _ => throw "out of fuel"
    | fuel + 1, statement, s, locals =>
      match statement with
      | .set name value => do pure (.on, s, locals.insert name (← value.run s locals))
      | .setGlobal name value => do
        pure (.on, { s with globals := s.globals.insert name (← value.run s locals) }, locals)
      | .setItem array i value => do
        let i ← i.run s locals
        let value ← value.run s locals
        match s.arrays[array]? with
        | none => throw s!"no array {array}"
        | some items =>
          if i.toNat < items.size then
            pure (.on, { s with arrays := s.arrays.insert array (items.set! i.toNat value) }, locals)
          else throw s!"{array}[{i}] is outside it"
      | .store address value => do
        let address ← address.run s locals
        if address % 8 != 0 then throw s!"a write at {address}, which is not a multiple of eight"
        pure (.on, { s with memory := s.memory.insert address (← value.run s locals) }, locals)
      | .branch condition yes no => do
        if (← condition.run s locals) != 0 then runAll p outside fuel yes s locals
        else runAll p outside fuel no s locals
      | .loop condition body => do
        if (← condition.run s locals) == 0 then pure (.on, s, locals) else
        match ← runAll p outside fuel body s locals with
        | (.on, s, locals) => Stmt.run p outside fuel (.loop condition body) s locals
        | ended => pure ended
      | .call result function arguments => do
        let values ← arguments.mapM (·.run s locals)
        match p.functions.find? (·.name == function) with
        | none => throw s!"no function {function}"
        | some f =>
          match ← runAll p outside fuel f.body s (bind {} f.parameters values) with
          | (.stopped why, s, _) => pure (.stopped why, s, locals)
          | (.gave value, s, _) => pure (.on, s, match result with | some name => locals.insert name value | none => locals)
          | (.on, s, _) => pure (.on, s, match result with | some name => locals.insert name 0 | none => locals)
      | .outside result c => do
        let (value, s) ← outside c s
        pure (.on, s, match result with | some name => locals.insert name value | none => locals)
      | .stop why => pure (.stopped why, s, locals)
      | .give value => do pure (.gave (← value.run s locals), s, locals)
  def runAll (p : Program) (outside : Outside) : Nat → List Stmt → State → Locals → Except String (Ending × State × Locals)
    | 0, _, _, _ => throw "out of fuel"
    | _, [], s, locals => pure (.on, s, locals)
    | fuel + 1, statement :: rest, s, locals => do
      match ← Stmt.run p outside fuel statement s locals with
      | (.on, s, locals) => runAll p outside fuel rest s locals
      | ended => pure ended
end

/-- A program's state before anything has run: every global zero, every array full of zeros. -/
def Program.start (p : Program) : State :=
  { arrays := p.arrays.foldl (fun arrays (name, size) => arrays.insert name (Array.replicate size 0)) {} }

/-- Calls a function by name. -/
def Program.call (p : Program) (outside : Outside) (fuel : Nat) (function : String) (arguments : List UInt64)
    (s : State) : Except String (Ending × State) :=
  match p.functions.find? (·.name == function) with
  | none => throw s!"no function {function}"
  | some f => do
    let (ending, s, _) ← runAll p outside fuel f.body s (bind {} f.parameters arguments)
    pure (ending, s)

end Mini
