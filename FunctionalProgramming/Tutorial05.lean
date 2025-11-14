import Mathlib.Tactic.Linarith

namespace Week05

-- Exercises to practice with.
-- 1. Add support for some more operators: and, or, not, div, mod.
-- 2. Implement some programs in this language, for example:
--   - compute the maximum of two numbers
--   - compute the gcd of two numbers
--   - compute the nth prime number
-- 3. Add support for reading user input.
-- 4. Right now, we need to write `liftState fail`.  Can you get around this with typeclasses?
-- 5. Add support for `save` (which stores all current variable values) and `load` (which restores them to their last values).
-- 6. Add support for lists as values.

inductive BinOp where
  | add | mul | sub | eq | lt | le
deriving instance Repr for BinOp

inductive Value where
  | nat (n : ℕ)
  | bool (b : Bool)
deriving instance Repr for Value

-- This allows us to use natural numbers and booleans as values.
instance : Coe ℕ Value where
  coe := .nat
instance : OfNat Value n where
  ofNat := .nat n
instance : Coe Bool Value where
  coe := .bool

instance : ToString Value where
  toString v := match v with
    | .nat n => toString n
    | .bool b => toString b

instance : Inhabited Value where
  default := .nat 0

mutual
  inductive Exp where
    | const (value : Value)
    | var (name : String)
    | bin_op (op : BinOp) (e₁ e₂ : Exp)
    | ifthenelse (ec et ee : Exp)
    | with_stmt (stmt : Stmt) (result : Exp)

  inductive Stmt where
    | exp_stmt (e : Exp)
    | assignment (name : String) (e : Exp) -- name = e
    | while (ec : Exp) (body : Stmt)
    | try_catch (try_body catch_body : Stmt)
    | print (e : Exp)
    | stmt_block (stmts : List Stmt)
end

-- Similar from Value to Exp and Exp to Stmt
instance : Coe Value Exp where
  coe := .const
instance : OfNat Exp n where
  ofNat := .const n
instance : Coe Exp Stmt where
  coe := .exp_stmt
-- And for variables
instance : Coe String Exp where
  coe := .var
-- And let's make blocks easier to work with
instance : Coe (List Stmt) Stmt where
  coe := .stmt_block

-- StateT Option σ α != State σ (Option α)
def InterpState (m : Type → Type) σ α := σ → m (α × σ)
def InterpFail (m : Type → Type) α := m (Option α)

instance [Monad m] : Monad (InterpState m σ) where
  pure a := fun s => pure ⟨ a, s ⟩
  bind isa f := fun s => do
    let ⟨ a, s' ⟩ ← isa s
    f a s'

instance [Monad m] : Monad (InterpFail m) where
  pure a :=
    let r: m (Option _) := pure $ some a
    r
  bind isa f :=
    let r: m (Option _) := do
      let r ← isa
      match r with
      | some a => f a
      | none => pure none
    r

def liftState [Monad m] (act : m α) : InterpState m σ α := fun s => do pure ⟨ ←act, s ⟩
def liftFail [Monad m] (act : m α) : InterpFail m α := (do pure $ some (←act) : m (Option _))

def get [Monad m] : InterpState m σ σ := fun s => pure ⟨ s , s ⟩
def put [Monad m] (new_s : σ) : InterpState m σ Unit := fun _ => pure ⟨ ⟨⟩, new_s ⟩
def modify' [Monad m] (f : σ → σ) : InterpState m σ Unit := do
  let V <- get
  put $ f V

def fail [Monad m] : InterpFail m α := (pure none : m (Option _))

abbrev Env := Std.HashMap String Value

abbrev Interp := InterpState (InterpFail IO)
def liftInterp : IO α → Interp σ α := liftState ∘ liftFail

-- Note that if we use InterpFail here, we won't be able to pass Interp as an input.
-- We will see how to fix this later.
def recover (interp1 interp2 : Interp σ α) : Interp σ α := fun s =>
  let r : IO (Option _) := do
    let oa ← interp1 s
    match oa with
    | some a => pure $ some a
    | none => interp2 s
  r

def BinOp.eval : BinOp → Value → Value → Interp Env Value
  | add, .nat n, .nat m => pure $ .nat (n + m)
  | mul, .nat n, .nat m => pure $ .nat (n * m)
  | sub, .nat n, .nat m => pure $ .nat (n - m)
  | eq, .bool b, .bool c => pure $ .bool (b = c)
  | eq, .nat n, .nat m => pure $ .bool (n = m)
  | lt, .nat n, .nat m => pure $ .bool (n < m)
  | le, .nat n, .nat m => pure $ .bool (n ≤ m)
  | _, _, _ => liftState fail

mutual
  partial def Exp.eval : Exp → Interp Env Value
    | .const value => pure value
    | .var name => do pure $ (←get)[name]?.getD default
    | .bin_op op e₁ e₂ => do
        let v₁ ← e₁.eval
        let v₂ ← e₂.eval
        op.eval v₁ v₂
    | .ifthenelse ec et ee => do
        let c ← ec.eval
        match c with
        | .bool true => et.eval
        | .bool false => ee.eval
        | _ => liftState fail
    | .with_stmt stmt result => do
        stmt.eval
        result.eval

  partial def runWhile (ec : Exp) (body : Stmt) : Interp Env Unit := do
    let c ← ec.eval
    match c with
    | .bool true =>
        body.eval
        runWhile ec body
    | .bool false => pure ⟨⟩
    | _ => liftState fail


  partial def Stmt.eval : Stmt → Interp Env Unit
    | .exp_stmt e => do
        let _ ← e.eval
        pure ⟨⟩
    | .assignment name e => do
        let v ← e.eval
        modify' fun V => V.insert name v
    | .while ec body => do
        runWhile ec body
    | .try_catch tb cb => recover tb.eval cb.eval
    | .print e => do
        let v ← e.eval
        liftInterp $ IO.println v
    | .stmt_block stmts => do
        forM stmts Stmt.eval
end

open Value
open Exp
open Stmt
open BinOp
-- Introduce a shorthand for assignment
infix:50 "::=" => assignment
infix:60 "=ⁱ" => bin_op eq
infix:60 "<ⁱ" => bin_op lt
infix:60 "≤ⁱ" => bin_op le
infix:70 "+ⁱ" => bin_op add
infix:70 "-ⁱ" => bin_op sub
infix:75 "*ⁱ" => bin_op mul
def program: Stmt := [
  "x" ::= 5,
  "i" ::= 0,
  "sum" ::= 0,
  .while ("i" <ⁱ "x") [
    "sum" ::= "sum" +ⁱ "i",
    "i" ::= "i" +ⁱ 1,
  ],
  print "sum",
]
def prog_action : IO (Option (Unit × Env)) := program.eval ∅
#eval prog_action

end Week05
