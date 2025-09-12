import LeanSearchClient.Basic
import Mathlib.Tactic.Linarith

namespace Lecture02

-- Turnstile, function types

example (n : ℕ) (m : ℕ) (h : n = m) : m = n := h.symm

def symmetry (n : ℕ) (m : ℕ) : n = m → m = n := fun h => h.symm

example : 3 = 3 := symmetry 3 3 (by rfl)

example (n : ℕ) (m : ℕ) : n = m → m = n := by
  intro h
  revert m
  sorry

-- Example: parametrising over a type


-- Introduction and elimination rules

-- Pair

#print Prod
#print Prod.mk
#print Prod.rec

-- recursor Prod.rec.{u_1, u, v} : {X : Type u} → {Y : Type v} →
-- {motive : X × Y → Sort u_1} →
-- ((fst : X) → (snd : Y) → motive (fst, snd)) →
-- (t : X × Y) → motive t

example (p : X × Y) : Prod.rec Prod.mk p = p := by
  reduce
  rfl

example (f : X → Y → Z) (x : X) (y : Y) :
  Prod.rec f (Prod.mk x y) = f x y := by
  reduce
  rfl

example (p : ℕ × ℕ) : ℕ :=
  match p with
  | Prod.mk a b => a + b

example (p : ℕ × ℕ) : ℕ :=
  Prod.rec (fun a b => a + b) p


-- Unit

#print Unit

#print Unit.unit
#print PUnit.unit
#print PUnit.rec

-- Empty

#print Empty

-- Sum

#print Sum

example (f : A → Z) (g : B → Z) (a : A) :
  Sum.rec f g (Sum.inl a) = f a := by
  reduce
  rfl

example (f : A → Z) (g : B → Z) (b : B) :
  Sum.rec f g (Sum.inr b) = g b := by
  reduce
  rfl

section
variable  {A B} (b : B)
#check (Sum.inr b : A ⊕ B)
end

def UU := Unit ⊕ Unit
def uul : UU := Sum.inl Unit.unit
def uur : UU := Sum.inr Unit.unit

-- aka Optional α
def Maybe α := α ⊕ Unit

-- Inductive types

inductive BinTree α where
  | node : BinTree α → BinTree α → BinTree α
  | leaf : α → BinTree α

#print BinTree
#print BinTree.rec
#print BinTree.casesOn

def BinTree.depth {α} : BinTree α → ℕ := fun bt =>
  match bt with
  | node l r => 1 + l.depth.max r.depth
  | leaf _ => 1

def BinTree.size {α} : BinTree α → ℕ
  | node l r => l.size + r.size + 1
  | leaf _ => 1

example (bt : BinTree α) : bt.depth ≤ bt.size := by
  induction bt with
  | node l r IHl IHr =>
      simp [BinTree.depth, BinTree.size]
      have : l.depth.max r.depth ≤ l.size + r.size := by
        simp
        constructor
        · linarith
        · linarith
      linarith
  | leaf _ =>
      simp [BinTree.depth, BinTree.size]

end Lecture02
