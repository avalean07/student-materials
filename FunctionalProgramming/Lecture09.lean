import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

namespace Lecture09

inductive Exp where
  | const (n : ℕ)
  | var (x : String)
  | add (lhs rhs : Exp)

abbrev Env := Std.HashMap String ℕ

@[reducible]
def Exp.eval (V : Env) : Exp → Option ℕ
  | .const n => some n
  | .var x => V[x]?
  | .add lhs rhs => do
      let v1 ← lhs.eval V
      let v2 ← rhs.eval V
      pure $ v1 + v2

-- Step V e1 e2: e1 can take one step to reach e2
inductive Step (V : Env) : Exp → Exp → Prop where
  | var_step : V[x]? = some k → Step V (.var x) (.const k)
  | add_step : k = kl + kr → Step V (.add (.const kl) (.const kr)) (.const k)
  | add_left : Step V e₁ e₁'
             → Step V (.add e₁ e₂) (.add e₁' e₂)
  | add_right : Step V e₂ e₂'
              → Step V (.add (.const kl) e₂) (.add (.const kl) e₂')

inductive Steps V : Exp → Exp → Prop where
  | trivial : Steps V e e
  | step : Step V e₁ e₂ → Steps V e₂ e₃ → Steps V e₁ e₃

def Steps.single : Step V e₁ e₂ → Steps V e₁ e₂ := sorry

instance : Trans (Steps V) (Steps V) (Steps V) where
  trans := sorry
instance : Trans (Step V) (Steps V) (Steps V) where
  trans := sorry
instance : Trans (Steps V) (Step V) (Steps V) where
  trans := sorry
instance : Trans (Step V) (Step V) (Steps V) where
  trans := sorry

@[refl]
lemma Steps.reflexive : Steps V e e := sorry

lemma add_left_of_steps
    : Steps V e₁ e₁'
    → Steps V (.add e₁ e₂) (.add e₁' e₂) := by
  sorry

lemma add_right_of_steps
    : Steps V e₂ e₂'
    → Steps V (.add (.const kl) e₂) (.add (.const kl) e₂') := by
  sorry


section
open Exp
def ex_V := (Std.HashMap.ofList [("x", 1)])
example : Steps ex_V
                (.add (.const 3) (.add (.var "x") (.const 5)))
                (.const 9) := by
  calc Steps ex_V _ (.add (.const 3) (.const 6)) := by
          apply add_right_of_steps
          calc Step ex_V _ (.add (.const 1) (.const 5)) := by
                  apply Step.add_left
                  constructor
                  unfold ex_V
                  simp
               Step ex_V _ _ := by
                  constructor
                  rfl
       Step  ex_V _ _ := by
          constructor
          rfl

end

lemma eval_eq_under_step
    : Step V e₁ e₂ → e₁.eval V = e₂.eval V := by
  sorry

theorem eval_eq_some_of_steps (V : Env)
    : Steps V e (.const n) → e.eval V = some n := by
  generalize result_eq : (Exp.const n) = result
  intro steps
  induction steps <;> cases result_eq
  · simp
  · rename_i e₁ e₂ step steps IH
    specialize (IH rfl)
    rw [eval_eq_under_step step]
    assumption

lemma lhs_eval_eq_some_of_eval_eq_some
    : (Exp.add lhs rhs).eval V = some n → ∃ kl, lhs.eval V = some kl := by
  intro eval_eq
  cases lhs_eval_eq : lhs.eval V
  case none => simp [Exp.eval, lhs_eval_eq] at eval_eq
  case some k => exists k

lemma rhs_eval_eq_some_of_eval_eq_some
    : (Exp.add lhs rhs).eval V = some n → ∃ kr, rhs.eval V = some kr := by
  intro eval_eq
  cases rhs_eval_eq : rhs.eval V
  case none => simp [Exp.eval, rhs_eval_eq] at eval_eq
  case some k => exists k

theorem steps_of_eval_eq_some (V : Env)
    : e.eval V = some n → Steps V e (.const n) := by
  intro eval_eq
  induction e generalizing n
  · simp only [Exp.eval] at eval_eq
    cases eval_eq
    constructor
  · apply Steps.single
    constructor
    simpa using eval_eq
  · have ⟨ kl, lsteps ⟩ := lhs_eval_eq_some_of_eval_eq_some eval_eq
    have ⟨ kr, rsteps ⟩ := rhs_eval_eq_some_of_eval_eq_some eval_eq
    rename_i lhs rhs lIH rIH
    calc Steps V _ (Exp.add (.const kl) rhs) := by
            apply_rules [add_left_of_steps, lIH]
         Steps V _ (Exp.add (.const kl) (.const kr)) := by
            apply_rules [add_right_of_steps, rIH]
         Step V _ _ := by
            constructor
            simp [Exp.eval, lsteps, rsteps] at eval_eq
            rw [eval_eq]

inductive OnlyVars (vars : List String) : Exp → Prop where
  | const : OnlyVars vars (.const n)
  | var : x ∈ vars → OnlyVars vars (.var x)
  | add : OnlyVars vars lhs → OnlyVars vars rhs
        → OnlyVars vars (lhs.add rhs)

def ContainsAll (vars : List String) (V : Env) := ∀ v, v ∈ vars → v ∈ V

theorem progress
    : OnlyVars vars e → ContainsAll vars V
    → (∃ n, e = .const n) ∨ (∃ e', Step V e e') := by
  intro onlyVars containsAll
  induction e
  case const n =>
    left
    exists n
  all_goals right
  case var x =>
    cases onlyVars
    have := containsAll _ (by assumption)
    exists .const V[x]
    constructor
    apply Std.HashMap.getElem?_eq_some_getElem
  case add lhs rhs lIH rIH =>
    cases onlyVars
    rename_i lvs rvs
    rcases lIH lvs with (⟨kl, rfl⟩ | ⟨ lhs', lsteps⟩)
    · rcases rIH rvs with (⟨kr, rfl⟩ | ⟨ rhs', rsteps⟩)
      · exists .const (kl + kr)
        constructor
        rfl
      · exists .add (.const kl) rhs'
        constructor
        assumption
    · exists .add lhs' rhs
      constructor
      assumption


theorem preservation
    : OnlyVars vars e → Step V e e'
    → OnlyVars vars e' := by
  intro onlyVars step
  induction step
  · constructor
  · constructor
  · cases onlyVars
    constructor
    · rename_i IH vl vr
      apply IH
      assumption
    · assumption
  · cases onlyVars
    constructor
    · assumption
    · rename_i IH vl vr
      apply IH
      assumption

theorem totality
    : OnlyVars vars e → ContainsAll vars V
    → ∃ k, Steps V e (.const k) := by
  intro onlyVars containsAll
  induction e
  · sorry
  · sorry
  · sorry

end Lecture09
