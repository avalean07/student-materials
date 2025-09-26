import Mathlib.Tactic.Linarith

/- Typeclasses -/

inductive MyList (α : Type) : Type where
  | nil
  | cons : α → MyList α → MyList α

def MyList.size : MyList α → ℕ
  | nil => 0
  | cons _ xs => 1 + xs.size

inductive MyTree α where
  | leaf
  | node : MyTree α → α → MyTree α → MyTree α

def MyTree.size : MyTree α → ℕ
  | leaf => 0
  | node lt _ rt => 1 + lt.size + rt.size

-- In Kotlin:
-- fun <T : Sizeable> example(t : T) { ... t.size() ... }

class Sizeable τ where
  size : τ → ℕ

open Sizeable


/-
-- equivalently:
def genericSize [Sizeable τ] : τ → ℕ := size
-/
def genericSize [Sizeable τ] : τ → ℕ :=
  fun t => Sizeable.size t

def ex1 : MyList ℕ := MyList.cons 5 MyList.nil

instance listSizable : Sizeable (MyList α) where
  size := MyList.size

-- alternative syntax:
instance treeSizable : Sizeable (MyTree α) := {
  size := MyTree.size
}

section
open MyTree
def tree_ex1 : MyTree ℕ := node (node leaf 1 leaf) 2 leaf
end

#eval genericSize ex1
#eval genericSize tree_ex1


/- Standard typeclasses -/

-- Add, HMul

set_option pp.notation false
#check 2 + 2
#print HAdd
#print Add
set_option pp.notation true

def MyList.zip (f : α → α → α) : MyList α → MyList α → MyList α
  | cons x xs, cons y ys => cons (f x y) (xs.zip f ys)
  | _, _ => nil

instance : Add (MyList ℕ) where
  add := MyList.zip (· + ·)

def MyList.toList : MyList α → List α
  | nil => []
  | cons x xs => x :: xs.toList

#eval ex1.toList
#eval (ex1 + ex1).toList
set_option pp.notation false
#check (_ + _)
#print HAdd.hAdd
-- #eval (tree_ex1 + tree_ex1)
set_option pp.notation true

def MyList.map (f : α → β) : MyList α → MyList β
  | nil => nil
  | cons x xs => cons (f x) (xs.map f)

instance : HMul ℕ (MyList ℕ) (MyList ℕ) where
  hMul n xs := xs.map (n * ·)

#eval ex1.toList
#eval (3 * ex1).toList

-- Inhabited

#print Inhabited
#check Inhabited.default

#eval (default : List ℕ)
#eval (default : ℕ)

#check List.get!
-- #check ([] : List Empty)[4]!

-- Decidable, BEq

#print Decidable
-- A prop is a type where every two elements are equal

example (P : Prop) (x y : P) : x = y := rfl

#print Or
example (p : P) (q : Q) : Or.inl p = Or.inr q := rfl

-- Isn't this a problem?
example : 0 = 1 := sorry
-- Idea:
-- define f : True ∨ True → ℕ
-- f (inl _) = 0
-- f (inr _) = 1
-- So our goal is f (inl True.intro) = f (inr True.intro)
-- since inl True.intro = inr True.intro, we rewrite the goal to
-- f (inl True.intro) = f (inl True.intro)
-- and we're done by rfl

/- Fails because ℕ is not a Prop
def f : True ∨ True → ℕ
  | Or.inl _ => 0
  | Or.inr _ => 1
-/

-- So: no, Prop is fine.

#check 0 = 1
set_option pp.notation false
#check if 0 = 1 then 3 else 5
set_option pp.notation true
#print ite

#check if 0 == 1 then 3 else 5
#print BEq

def ex_eq (n m : ℕ) : n ≤ m → m ≤ n → n = m := sorry -- provable
def ex_beq (n m : ℕ) : n ≤ m → m ≤ n → n == m := sorry -- provable

-- Functor, Applicative, Monad

#print Functor

instance : Functor MyList where
  map := MyList.map

def MyTree.map (f : α → β) : MyTree α → MyTree β
  | leaf => leaf
  | node lt x rt => node (lt.map f) (f x) (rt.map f)

instance : Functor MyTree where
  map := MyTree.map

def functorLawId (xs : List α) : xs.map id = xs := by
  induction xs
  · rfl
  · simp

def functorLawComposition
    (f : α → β) (g : β → γ) (xs : List α)
    : (xs.map f).map g = xs.map (g ∘ f) := by sorry

#print Applicative

def MyList.append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | cons x xs, ys => cons x (xs.append ys)

instance : Append (MyList α) where
  append := MyList.append

def MyList.pure : α → MyList α := (cons · nil)
def MyList.seq : MyList (α → β) → (Unit → MyList α) → MyList β
  | nil, _ => nil
  | cons f fs, xs => (xs ⟨⟩).map (fun x => f x) ++ fs.seq xs

instance : Applicative MyList where
  pure := MyList.pure
  seq := MyList.seq

def MyList.bind : MyList α → (α → MyList β) → MyList β
  | nil, _ => nil
  | cons x xs, f => f x ++ xs.bind f

instance : Monad MyList where
  bind := MyList.bind

/- Syntactic sugar -/

def pick2 (xs : MyList ℕ) : MyList (ℕ × ℕ) :=
  xs.bind fun x1 => xs.bind fun x2 => pure ⟨ x1, x2 ⟩

def pick2' (xs : MyList ℕ) : MyList (ℕ × ℕ) := do
  let x1 <- xs
  let x2 <- xs
  pure ⟨ x1, x2 ⟩

section
open MyList
#eval (pick2 (cons 1 (cons 2 nil))).toList
#eval (pick2' (cons 1 (cons 2 nil))).toList
end
