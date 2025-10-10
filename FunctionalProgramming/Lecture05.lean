import Mathlib.Tactic.Linarith

inductive BinOp where
  | add | mul | sub | eq | lt | le
deriving instance Repr for BinOp

inductive Value where
  | nat (n : ℕ)
  | bool (b : Bool)
deriving instance Repr for Value

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
    | block (stmts : List Stmt) (result : Exp)

  inductive Stmt where
    | exp_stmt (e : Exp)
    | assignment (name : String) (e : Exp) -- name = e
    | while (ec : Exp) (body : Stmt)
    | try_catch (try_body catch_body : Stmt)
    | print (e : Exp)
end

-- pure : α → M α
-- bind : M α → (α → M β) → M β

-- StateM σ α := σ → α × σ

/-
do
let x <- a
let y <- b
pure (f x y)

is translated to
bind a fun x => bind b fun y => pure (f x y)
-/

#print IO.print

abbrev Env := Std.HashMap String Value
def Interp σ α := σ → IO (Option (α × σ))

instance : Functor (Interp σ) where
  map f interp := fun s => do
    let r ← interp s
    match r with
    | some ⟨ a , s' ⟩ => pure (some ⟨ f a , s' ⟩)
    | none => pure none

instance : Monad (Interp σ) where
  pure a := fun s => pure $ some ⟨ a, s ⟩
  bind interp f := fun s => do
    let r ← interp s
    match r with
    | some ⟨ a, s' ⟩ => f a s'
    | none => pure none

def get : Interp σ σ := fun s => pure $ some ⟨ s , s ⟩
def put (new_s : σ) : Interp σ Unit := fun _ => pure $ some ⟨ ⟨⟩, new_s ⟩
def fail : Interp σ α := fun _ => pure $ none
def recover (interp1 interp2 : Interp σ α) : Interp σ α := fun s => do
  let r ← interp1 s
  match r with
  | some r => pure $ some r
  | none => interp2 s
def liftIO (act : IO α) : Interp σ α := fun s => do
  let a ← act
  pure $ some ⟨ a , s ⟩

def modify' (f : σ → σ) : Interp σ Unit := do
  let V <- get
  put $ f V

def BinOp.eval : BinOp → Value → Value → Interp Env Value
  | add, .nat n, .nat m => pure $ .nat (n + m)
  | mul, .nat n, .nat m => pure $ .nat (n * m)
  | sub, .nat n, .nat m => pure $ .nat (n - m)
  | eq, .bool b, .bool c => pure $ .bool (b = c)
  | eq, .nat n, .nat m => pure $ .bool (n = m)
  | lt, .nat n, .nat m => pure $ .bool (n < m)
  | le, .nat n, .nat m => pure $ .bool (n ≤ m)
  | _, _, _ => fail

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
        | _ => fail
    | .block stmts result => do
        forM stmts Stmt.eval
        result.eval

  partial def runWhile (ec : Exp) (body : Stmt) : Interp Env Unit := do
    let c ← ec.eval
    match c with
    | .bool true =>
        body.eval
        runWhile ec body
    | .bool false => pure ⟨⟩
    | _ => fail


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
        liftIO $ IO.println v
end

/-
-- What if inhabited was not required?
partial def fix (f : α → α) : α := f (fix f)
example False := fix (fun x => x)
-/

open Value
open Exp
open Stmt
open BinOp
def x_val := const (.nat 5)
def y_val := (const (.nat 2)).bin_op add (const (.nat 4))
def result_expr := (var "x").bin_op mul (var "y")
#eval (block [print (const (nat 5)), print (const (nat 7))] (const (nat 0))).eval ∅
