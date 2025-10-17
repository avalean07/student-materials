import Mathlib.Tactic.Linarith

--
-- The main types we work with
--

inductive BinTree (α : Type) where
  | leaf
  | node (a : α) (lst rst : BinTree α)

inductive WithBounds (α : Type) where
  | min
  | el (a : α)
  | max

--
-- Helper types
--

-- Extend this typeclass with properties you need.
class ValidElemType (α : Type) extends LT α, Ord α, BEq α where
  compare_eq_correct : ∀ a : α, compare a a = .eq
  beq_correct : ∀ a : α, (a == a) = true

variable {α : Type} [ValidElemType α]

inductive BinTreeElem (a : α) : BinTree α → Prop where
  | node_here : BinTreeElem a (.node a lst rst)
  | node_left : BinTreeElem a lst → BinTreeElem a (.node a' lst rst)
  | node_right : BinTreeElem a rst → BinTreeElem a (.node a' lst rst)

inductive WithBounds.LessThan : WithBounds α → WithBounds α → Prop where
  | min_el : LessThan .min (.el a)
  | min_max : LessThan .min .max
  | el_preserved : a < a' → LessThan (.el a) (.el a')
  | el_max : LessThan (.el a) .max

--
-- Typeclasses and helpful stuff for them
--

instance : Membership α (BinTree α) where
  mem t a := BinTreeElem a t

instance : Ord (WithBounds α) where
  compare x y := match x, y with
    | .min, .min => .eq
    | .max, .max => .eq
    | .min, _ => .lt
    | .max, _ => .gt
    | _, .min => .gt
    | _, .max => .lt
    | .el al, .el ar => compare al ar

instance : BEq (WithBounds α) where
  beq x y := compare x y == .eq

instance : LT (WithBounds α) where
  lt := WithBounds.LessThan

def between low (a : α) upp := low < WithBounds.el a ∧ WithBounds.el a < upp

--
-- Algorithms
--

def BinTree.size : BinTree α → ℕ
  | .leaf => 0
  | .node _ lst rst => 1 + lst.size + rst.size

def BinTree.insert (a : α) : BinTree α → BinTree α
  | .leaf => .node a .leaf .leaf
  | .node a' lst rst => match compare a a' with
      | .lt => .node a' (lst.insert a) rst
      | .eq => .node a' lst rst
      | .gt => .node a' lst (rst.insert a)

def BinTree.linear_contains (a : α) : BinTree α → Bool
  | .leaf => false
  | .node a' lst rst => a == a' || lst.linear_contains a || rst.linear_contains a

def BinTree.contains (a : α) : BinTree α → Bool
  | .leaf => false
  | .node a' lst rst => match compare a a' with
      | .lt => lst.contains a
      | .eq => true
      | .gt => rst.contains a

--
-- Properties for reasoning about algorithms
--

inductive BSTNode : WithBounds α → WithBounds α → BinTree α → Prop where
  | leaf : BSTNode low upp .leaf
  | node : BSTNode low (.el a) lst → BSTNode (.el a) upp rst
          → between low a upp
          → BSTNode low upp (.node a lst rst)

def BST (t : BinTree α) : Prop := BSTNode .min .max t

--
-- Lemmas and theorems
--

-- Exercise: complete the proof
theorem linear_contains_finds_if_present
    (a : α) (t : BinTree α) : a ∈ t → t.linear_contains a = true := by
  intro Hin
  induction Hin with
  | node_here =>
      unfold BinTree.linear_contains
      rewrite [ValidElemType.beq_correct]
      simp
  | node_left Hinl lIH =>
      unfold BinTree.linear_contains
      rewrite [lIH]
      simp
  | node_right => sorry

-- Exercise: prove tihs
theorem present_if_linear_contains_finds
    (a : α) (t : BinTree α) : t.linear_contains a = true → a ∈ t := by sorry

-- Exercise: complete the proof
theorem contains_finds_if_present_helper
    {a : α} {t : BinTree α} (tv : BSTNode low upp t)
    (cont : between low a upp)
    : a ∈ t → t.contains a = true := by
  intro Hin
  induction Hin generalizing low upp with
  | node_here =>
      sorry
  | node_left Hinl lIH =>
      cases tv
      sorry
  | node_right => sorry

theorem contains_finds_if_present
    (a : α) (t : BinTree α) (tv : BST t)
    : a ∈ t → t.contains a = true := by
  apply (contains_finds_if_present_helper tv)
  repeat constructor

-- Exercise: prove this
theorem present_if_contains_finds
    (a : α) (t : BinTree α) (tv : BST t)
    : t.contains a = true → a ∈ t := by sorry



-- Exercise: show that the natural numbers are a valid element type.
instance : ValidElemType ℕ where
  compare_eq_correct := sorry
  beq_correct := sorry
