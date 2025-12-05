import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Std.Data.HashMap

namespace Lecture11

variable (α : Type)
variable (β : α → Type)
variable (f : (x : α) → β x)
variable (a : α)

#check f a

-- fun x => body(x) : (x : α) → β(x)
-- (fun x => body(x)) a = body(a)
-- (fun x => body(x)) a : β(a)

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons : α → Vec α k → Vec α (k+1)

#print Vec
#print Vec.rec

@[reducible] def sum_manual : ∀ n, Vec ℕ n → ℕ := fun n v0 =>
  match v0 with
  | .nil => 0
  | .cons i v => i + sum_manual _ v

@[reducible] def recursor.{u} {α} (motive : ∀ k, Vec α k → Sort u)
    (nil_case : motive 0 .nil)
    (cons_case :
      ∀ {k}, (a : α) → (v : Vec α k) → motive k v → motive (k+1) (.cons a v))
    : ∀ k, (v : Vec α k) → motive k v := fun k v =>
  match v with
  | .nil => nil_case
  | .cons a v' => cons_case a v' (recursor motive nil_case cons_case _ v')

@[reducible] def sum_recursor : ∀ n, Vec ℕ n → ℕ :=
  recursor (fun _ _ => ℕ) 0 (fun i _ r => i + r)

def sum_equiv_rec : ∀ n, (v : Vec ℕ n)
    → sum_manual n v = sum_recursor n v :=
  recursor (fun n v => sum_manual n v = sum_recursor n v)
    (by simp)
    (by
      intro k a v ih
      simpa using ih)

def sum_equiv_ind : ∀ n, (v : Vec ℕ n)
    → sum_manual n v = sum_recursor n v := by
  intro n v
  induction v with
  | nil => simp
  | cons a v' ih =>
      unfold sum_manual
      unfold sum_recursor
      unfold recursor
      rewrite [ih]
      unfold sum_recursor
      rfl

def zeroes : (n : ℕ) → Vec ℕ n := fun n =>
  match n with
  | .zero => .nil
  | .succ k => .cons 0 (zeroes k)

-- zeroes 5 = [0, 0, 0, 0, 0]

-- zeroes 5
--   =
-- (fun n => match n with
--            | .zero => .nil
--            | .succ k => .cons 0 (zeroes k)) 5
--   =
-- (match 5 with
--   | .zero => .nil
--   | .succ k => .cons 0 (zeroes k))

-- zeroes : (n : ℕ) → Vec ℕ n
-- zeroes 5 : Vec ℕ 5

variable (P : ∀ {n}, Vec ℕ n → Prop)
example : P (zeroes l) := by
  unfold zeroes
  sorry

-- n, m : ℕ ⊢ n + m : ℕ
-- n : ℕ ⊢ zeroes n : Vec ℕ n

--          Γ, x : T ⊢ e(x) : S x
--  --------------------------------
--    Γ ⊢ fun x => e(x) : (x : T) → S x

-- n, m : ℕ ⊢ n + m : ℕ
-- we get: m : ℕ ⊢ fun n => n + m : (n : ℕ) → ℕ
-- equivalently: m : ℕ ⊢ fun n => n + m : ℕ → ℕ

-- n : ℕ ⊢ zeroes n : Vec ℕ n
-- we get: ⊢ fun n => zeroes n : (n : ℕ) → Vec ℕ n

structure Array (α : Type) where
  length : ℕ
  data : Vec α length

example : Array ℕ := ⟨ 5, zeroes 5 ⟩
example : Array ℕ := ⟨ 3, zeroes _ ⟩

def f1 (n : ℕ) := 5
def f2 : ℕ → ℕ
  | .zero => 5
  | .succ _ => 5

example : ∀ k, f1 k = f2 k := by
  intro k
  -- rfl
  sorry

def n := 5
example : n = 5 := rfl
example : ∀ (n m : ℕ), n + m = m + n := by
  -- rfl
  sorry
example : ∀ (n m : ℕ), n = m → m = n := by
  sorry


example (n : ℕ) : n + 1 = 0 → n + 1 = n := by
  intro h
  simp
  simp at h

end Lecture11
