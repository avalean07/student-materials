import Mathlib.Data.Nat.Notation
import Std.Data.HashMap

namespace Lecture10

-- x      variable use
-- e₁ e₂  function application
-- λx. e  anonymous functions
--
-- (λx. e₁) e₂ ~> e₁[x |-> e₂]
--
-- when evaluating ef ea
-- strict:
-- 1. evaluate ef to some (λx. eb)
-- 2. evaluate ea to some value v
-- 3. evaluate eb[x |-> v]
--
-- lazy:
-- 1. evaluate ef to some (λx. eb)
-- 2. evaluate eb[x |-> ea]
--
-- weird:
-- 1. evaluate ef to some (λx. eb)
-- 2. evaluate eb (‽)
-- 3. evaluate ea?


inductive BinOp where | add | mul | app

mutual
  inductive Value where
    | nat (n : ℕ)
    | closure (x : String) (body : Exp)

  inductive Exp where
    | value (v : Value)
    | const (n : ℕ)
    | var (x : String)
    | binOp (op : BinOp) (lhs rhs : Exp)
    | abs (x : String) (body : Exp)
end

-- e.subst x v: e with all occurences of x replaced by v
def Exp.subst (x₀ : String) (v₀ : Value) : Exp → Exp
  | .value v => .value v
  | .const n => .const n
  | .var x => if x == x₀ then .value v₀ else .var x
  | .binOp op lhs rhs => .binOp op (lhs.subst x₀ v₀) (rhs.subst x₀ v₀)
  | .abs x body => if x == x₀
                   then .abs x body
                   else .abs x (body.subst x₀ v₀)

-- C[·] is an execution context
-- i.e. C[e] is an expression
-- and if e can step, then C[e] can step
inductive ExCtx1 where
  -- C[·] = binOp op · rhs
  | binOpLeft (op : BinOp) (rhs : Exp)
  -- C[·] = binOp op v ·
  | binOpRight (op : BinOp) (v : Value)

def ExCtx := List ExCtx1
-- (C[·], e) |-> C[e]
def ExCtx1.fill (e : Exp) : ExCtx1 → Exp
  | .binOpLeft op rhs => .binOp op e rhs
  | .binOpRight op v => .binOp op (.value v) e
def ExCtx.fill (e : Exp) : ExCtx → Exp := List.foldr (flip ExCtx1.fill) e

abbrev Env := Std.HashMap String Value

inductive BinOpStep : BinOp → Value → Value → Exp → Prop
  | add_step : BinOpStep .add (.nat ln) (.nat rn) (.value (.nat (ln + rn)))
  | mul_step : BinOpStep .mul (.nat ln) (.nat rn) (.value (.nat (ln * rn)))
  | app_step
      -- (λx. body) v ~> body[x |-> v]
      (eq : e = body.subst x v)
      : BinOpStep .app (.closure x body) v e

inductive HeadStep : Exp → Exp → Prop
  | const_step : HeadStep (.const n) (.value (.nat n))
  | bin_op_step
      : BinOpStep op lv rv e
      → HeadStep (.binOp op (.value lv) (.value rv)) e
  | abs_step
      : HeadStep (.abs x body) (.value (.closure x body))

inductive Step : Exp → Exp → Prop
  | ctx_step (ctx : ExCtx)
      (eq_e₁ : e₁' = ctx.fill e₁) (eq_e₂ : e₂' = ctx.fill e₂)
      -- if e₁ ~> e₂, then C[e₁] ~> C[e₂]
      : HeadStep e₁ e₂
      → Step e₁' e₂'

inductive RTC (R : Exp → Exp → Prop) : Exp → Exp → Prop where
  | trivial : RTC R e e
  | step : R e₁ e₂ → RTC R e₂ e₃ → RTC R e₁ e₃

abbrev Steps := RTC Step

-- Γ ⊢ e : T   "e has type T in context Γ"
inductive Ty where
  | nat
  | fn (argTy retTy : Ty)

abbrev TyCtx := Std.HashMap String Ty

mutual
  inductive BinOp.TyJdg : BinOp → Ty → Ty → Ty → Prop where
    | add_ty : BinOp.TyJdg .add .nat .nat .nat
    | mul_ty : BinOp.TyJdg .add .nat .nat .nat
    | app_ty : BinOp.TyJdg .add (.fn argTy retTy) argTy retTy

  inductive Value.TyJdg : TyCtx → Value → Ty → Prop where
    | nat_ty : Value.TyJdg Γ (.nat n) .nat
    | closure_ty
        : Exp.TyJdg (Γ.insert x argTy) body retTy
        → Value.TyJdg Γ (.closure x body) (.fn argTy retTy)

  inductive Exp.TyJdg : TyCtx → Exp → Ty → Prop where
    | value_ty : v.TyJdg Γ ty → Exp.TyJdg Γ (.value v) ty
    | const_ty : Exp.TyJdg Γ (.const n) .nat
    | var_ty : Γ[x]? = some ty → Exp.TyJdg Γ (.var x) ty
    | bin_op_ty
        : BinOp.TyJdg op lhsTy rhsTy ty
        → lhs.TyJdg Γ lhsTy
        → rhs.TyJdg Γ rhsTy
        → Exp.TyJdg Γ (.binOp op lhs rhs) ty
    | abs_ty
        : Exp.TyJdg (Γ.insert x argTy) body retTy
        → Exp.TyJdg Γ (.abs x body) (.fn argTy retTy)
end

theorem progress
    : e.TyJdg ∅ ty → (∃ v, e = .value v) ∨ (∃ e', Step e e') := by sorry

theorem preservation
    : e.TyJdg ∅ ty → Step e e' → e'.TyJdg ∅ ty := by sorry

-- (λx. x) 5
example : Steps (.binOp .app (.abs "x" (.var "x")) (.const 5)) (.value (.nat 5)) := by
  apply RTC.step
  · apply Step.ctx_step [.binOpLeft .app (.const 5)] rfl rfl
    apply HeadStep.abs_step
  apply RTC.step
  · apply Step.ctx_step [.binOpRight .app (.closure "x" (.var "x"))] rfl rfl
    apply HeadStep.const_step
  simp [ExCtx.fill, flip, ExCtx1.fill]
  apply RTC.step
  · apply Step.ctx_step [] rfl rfl
    apply HeadStep.bin_op_step
    apply BinOpStep.app_step rfl
  simp [ExCtx.fill]
  simp [Exp.subst]
  apply RTC.trivial

example : Steps (.binOp .add (.const 2) (.const 2)) (.value (Value.nat 4)) := by
  apply RTC.step
  · apply Step.ctx_step [.binOpLeft .add (.const 2)] rfl rfl
    apply HeadStep.const_step
  apply RTC.step
  · apply Step.ctx_step [.binOpRight .add (.nat 2)] rfl rfl
    apply HeadStep.const_step
  apply RTC.step
  · apply Step.ctx_step [] rfl rfl
    apply HeadStep.bin_op_step
    apply BinOpStep.add_step
  apply RTC.trivial

end Lecture10
