import Mathlib.Tactic.Linarith

inductive WithBounds (α : Type) where
  | min
  | el (a : α)
  | max
  deriving DecidableEq

variable {α : Type}

inductive WithBounds.LessEqual [LE α] : WithBounds α → WithBounds α → Prop where
  | min_all : LessEqual .min b
  | el_el : a ≤ a' → LessEqual (.el a) (.el a')
  | all_max : LessEqual a .max

instance [LE α] : LE (WithBounds α) where
  le := WithBounds.LessEqual

theorem WithBounds.LessEqual.trans [LE α] [inst : @Trans α α α LE.le LE.le LE.le] (a b c : WithBounds α) :
    a ≤ b → b ≤ c → a ≤ c := by
  intro H1 H2
  cases H1 <;> cases H2 <;> constructor
  apply inst.trans <;> assumption

instance [Preorder α] : Preorder (WithBounds α) where
  le_refl := by rintro (_ | _ | _) <;> constructor; apply le_refl
  le_trans := WithBounds.LessEqual.trans

instance [PartialOrder α] : PartialOrder (WithBounds α) where
  le_antisymm a b Hab Hba := by
    cases Hab <;> cases Hba <;> try rfl
    congr
    apply le_antisymm <;> assumption

variable [LinearOrder α]

instance : LinearOrder (WithBounds α) where
  le_total a b := by
    cases a
    · left; constructor
    · rename_i a
      cases b
      · right; constructor
      · rename_i a'
        cases (le_total a a')
        · left; constructor; assumption
        · right; constructor; assumption
      · left; constructor
    · right; constructor
  toDecidableLE := by
    rintro (_ | a | _) (_ | b | _) <;> (try (right; constructor; done)) <;> (try (left; rintro (_|_); done))
    by_cases (a ≤ b)
    · right; constructor; assumption
    · left; rintro (_|_); contradiction

instance : Trans LE.le LE.le (LE.le : WithBounds α → WithBounds α → Prop) where
  trans := le_trans

instance : Trans LT.lt LT.lt (LT.lt : WithBounds α → WithBounds α → Prop) where
  trans := lt_trans

@[simp] lemma WithBounds.el_lt_iff_lt (a b : α) : WithBounds.el a < WithBounds.el b ↔ a < b := by
  constructor
  · intro ⟨ _, Hnba ⟩
    cases (lt_or_ge a b) <;> try assumption
    exfalso
    apply Hnba
    constructor
    assumption
  · intro Hab
    rw [lt_iff_le_and_ne]
    constructor
    · constructor
      apply le_of_lt
      assumption
    · intro H
      revert Hab
      cases H
      apply lt_irrefl

@[simp] lemma WithBounds.min_lt_el {a : α} : WithBounds.min < WithBounds.el a := by
  rewrite [lt_iff_le_and_ne]; tauto

@[simp] lemma WithBounds.min_min {b : WithBounds α} : WithBounds.min ≤ b := LessEqual.min_all

@[simp] lemma WithBounds.el_lt_max {a : α} : WithBounds.el a < WithBounds.max := by
  rewrite [lt_iff_le_and_ne]; tauto

@[simp] lemma WithBounds.max_max {b : WithBounds α} : b ≤ WithBounds.max := LessEqual.all_max

def between low (a : α) upp := low < WithBounds.el a ∧ WithBounds.el a < upp

lemma between_change_upp {a : α} (H : .el a < upp')
    : between low a upp → between low a upp' := fun ⟨ hl, _ ⟩ => ⟨ hl, H ⟩

lemma between_change_low {a : α} (H : low' < .el a)
    : between low a upp → between low' a upp := fun ⟨ _, hr ⟩ => ⟨ H, hr ⟩

lemma between_weaken_both {a : α} {low upp} (Hlow : low' ≤ low) (Hupp : upp ≤ upp')
    : between low a upp → between low' a upp' := by
  rintro ⟨ hl, hr ⟩
  constructor
  · apply lt_of_le_of_lt <;> assumption
  · apply lt_of_lt_of_le <;> assumption

lemma between_weaken_upp {a : α} upp (H : upp ≤ upp')
    : between low a upp → between low a upp' := by
  apply between_weaken_both <;> trivial


lemma between_weaken_low {a : α} low (H : low' ≤ low)
    : between low a upp → between low' a upp := by
  apply between_weaken_both <;> trivial

lemma between_rotate_right {a1 a2 : α}
    : between low a1 (.el a2) → between low a2 upp → between (.el a1) a2 upp := by
  rintro ⟨⟩
  apply between_change_low
  assumption

lemma between_rotate_left {a1 a2 : α}
    : between (.el a1) a2 upp → between low a1 upp → between low a1 (.el a2) := by
  rintro ⟨⟩
  apply between_change_upp
  assumption

lemma between_rotate_right' {a1 a2 : α}
    : between low a1 upp → between (.el a1) a2 upp → between low a2 upp := by
  rintro ⟨⟩
  apply between_weaken_low
  apply le_of_lt
  assumption

lemma between_rotate_left' {a1 a2 : α}
    : between low a2 upp → between low a1 (.el a2) → between low a1 upp := by
  rintro ⟨⟩
  apply between_weaken_upp
  apply le_of_lt
  assumption
