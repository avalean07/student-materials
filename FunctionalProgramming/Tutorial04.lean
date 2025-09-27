import Mathlib.Tactic.Linarith

-- Take the following structure:
structure Vec2D where
  x : ℕ
  y : ℕ

-- Define vector-vector addition and scalar-vector multiplication
-- and create the corresponding instances.

instance : Add Vec2D where
  add v1 v2 := {x := v1.x + v2.x, y := v1.y + v2.y}

instance : HMul ℕ Vec2D Vec2D where
  hMul n v := {x := n * v.x, y := n * v.y}

#eval ( {x := 1, y := 2} : Vec2D ) + ( {x := 3, y := 4} : Vec2D )
#eval 3 * ( {x := 2, y := 5} : Vec2D )

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

open MyOption

instance : Functor MyOption where
  map f
   | MyOption.none => MyOption.none
   | MyOption.some x => MyOption.some (f x)

def MyOption.pure (x : α) : MyOption α := MyOption.some x

def MyOption.seq (f : MyOption (α → β )) (x: Unit → MyOption α) : MyOption β :=
  match f with
  | none => none
  | some g => match x () with
              | none => none
              | some a => some (g a)

instance : Applicative MyOption where
  pure := MyOption.pure
  seq := MyOption.seq

def MyOption.bind (x: MyOption α) (f : α → MyOption β) : MyOption β :=
  match x with
  | MyOption.none => MyOption.none
  | MyOption.some a => f a


def MyReader (ρ α : Type) : Type := ρ → α

-- Complete the definition.
def listen : MyReader ρ ρ := fun ρ => ρ

def MyState (σ α : Type) : Type := σ → (σ × α)

-- Complete the definitions.
def get : MyState σ σ := fun s => (s, s)
def put (s : σ) : MyState σ Unit := fun _ => (s, ())

instance : Functor (MyState σ) where
  map f ma := fun s =>
    let (s', a) := ma s
    (s', f a)

instance : Applicative (MyState σ ) where
  pure a := fun s => (s, a)
  seq mf ma := fun s =>
    let(s', g) := mf s
    let (s'', a) := (ma ()) s'
    (s'', g a)

instance : Monad (MyState σ ) where
  pure a := fun s => (s, a)
  bind ma f := fun s =>
    let(s', a) := ma s
    f a s'


-- Try various combinations like MyReader σ ∘ MyOption
-- (you may want to define them explicitly).
-- Which ones have Functor, Applicative, and Monad instances?

-- Complete the definition: make a function that take as a condition and a body,
-- and runs the body as long as the condition is true.

def runWhile {σ : Type} (fuel : Nat) (cond : MyState σ Bool) (body : MyState σ Unit) : MyState σ Unit := do
  let rec loop (k : Nat) : MyState σ Unit :=
    match k with
    | 0     => pure ()
    | k+1   => do
      let b ← cond
      if b then
        body
        loop k
      else
        pure ()
  loop fuel

-- Use do notation and the MyState monad instance to compute the
-- Fibonacci numbers imperatively.

def fibState (n : Nat) : MyState  (Nat × Nat × Nat) Unit := do
  let rec aux (k : Nat) : MyState (Nat × Nat × Nat) Unit :=
  match k with
  | 0 => pure ()
  | k+1  => do
    let (a, b, i) <- get
    put (b, a + b, i+1)
    aux k
  aux n

#eval (fibState 5) (0, 1, 0)
