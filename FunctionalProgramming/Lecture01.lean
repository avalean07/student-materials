import Mathlib.Tactic.Linarith

namespace Week01

/-
# Computations in the IDE

Use `#eval` to find the value of an expression.
-/

#eval 2 + 2
#eval 3 + 3
#eval "Hello " ++ "world!"

/-
# Types

Use #check to find the type of an expression.

Some types to be aware of:
- `Nat` (or `ℕ`): the natural numbers (0, 1, 2, ...)
- `String`: strings of text
- `A → B`: functions from A to B
-/

#check (String.append : (String -> (String -> String)))

variable (A B C : Type)
variable (f : A -> B -> C)
variable (x : A) (y : B)

#check f x

#check fun (n : Nat) => fun (k : Nat) => n + k
#eval (fun (n : Nat) => fun (k : Nat) => n + k) 3 5

/-
# Definitions

General syntax:
  def name (param : Type) : Type := definition

To see the definition of a name, use #print
-/

-- Examples...
def five : Nat := 5
def five' := 5
def four : Nat := 2 + 2
def plusOne (k : Nat) : Nat := k + 1
def plusOne' (k : Nat) := k + 1
def plusOne'' : Nat → Nat := fun k => k + 1

#print plusOne
#print String.append

-- Example: Identity
def id' {α : Type} (x : α) := x
#eval id' 4
def id'' (α : Type) (x : α) := x
#eval id'' Nat 5

-- Example: maximum
def maximum (n m : Nat) : Nat :=
  if n ≤ m then m else n

/-
# Proofs
-/

example : maximum 3 5 = 5 := by
  reduce
  rfl

example (n : Nat) : maximum n (n + 1) = n + 1 := by
  rw [maximum]
  have n_le_nplus1 : n ≤ n + 1 := by linarith
  rw [if_pos n_le_nplus1]

theorem maximum_ge_fst (n k : Nat) : maximum n k >= n := by
  simp [maximum]
  split
  · assumption
  · rfl

/-
# Propositional Logic

Lean includes the usual logical connectives you're familiar with
from your mathematics courses.

- → implication (if-then)
- ∧ conjunction (and)
- ∨ disjunction (or)
- ¬ negation (not)

Note that ¬P is the same as P → False
-/

variable (P Q R : Prop)

example : P → P := fun p => p
example : P → P := by
  intro p
  exact p

#print And

example : And P Q → P := fun pq =>
  match pq with
  | And.intro p q => p

#print Or

example : Or P P → P := fun pp =>
  match pp with
  | Or.inl p1 => p1
  | Or.inr p2 => p2

example : P ∧ Q → P := by
  intro pq
  cases pq
  assumption

theorem pq_to_p : P ∧ Q → P := by tauto

#print pq_to_p


/-
# First-order logic

Lean also has support for first-order quantifiers:
- ∀ universal quantification (for all)
- ∃ existential quantification (there exists)
-/

example : ∀ (n : Nat), ∃ (k : Nat), n ≤ k := by
  intro n
  exists n + 1
  linarith

end Week01
