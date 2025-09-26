import Mathlib.Tactic.Linarith

-- Take the following structure:
structure Vec2D where
  x : ℕ
  y : ℕ

-- Define vector-vector addition and scalar-vector multiplication
-- and create the corresponding instances.

/-
Exercises:
- Define Functor, Applicative, and Monad instances for:
  - MyTree
  - MyOption
  - MyReader ρ
  - MyState σ
-/

inductive MyOption (α : Type) : Type where
  | none
  | some : α → MyOption α

def MyReader (ρ α : Type) : Type := ρ → α

-- Complete the definition.
def listen : MyReader ρ ρ := sorry

def MyState (σ α : Type) : Type := σ → (σ × α)

-- Complete the definitions.
def get : MyState σ σ := sorry
def put : σ → MyState σ Unit := sorry

-- Try various combinations like MyReader σ ∘ MyOption
-- (you may want to define them explicitly).
-- Which ones have Functor, Applicative, and Monad instances?

-- Complete the definition: make a function that take as a condition and a body,
-- and runs the body as long as the condition is true.
def runWhile (cond : MyState σ Bool) (body : MyState σ Unit) : MyState σ Unit := sorry

-- Use do notation and the MyState monad instance to compute the
-- Fibonacci numbers imperatively.
