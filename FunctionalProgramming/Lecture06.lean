import Mathlib.Tactic.Linarith

namespace Lecture

class ValidElemType (α : Type) extends LT α, Ord α, BEq α where
  compare_eq_correct : ∀ a : α, compare a a = .eq
  beq_correct : ∀ a : α, (a == a) = true

inductive Tree (α : Type) where
  | leaf
  | node (a : α) (lst rst : Tree α)

def Tree.size : Tree α → ℕ
  | .leaf => 0
  | .node _ lst rst => 1 + lst.size + rst.size

def Tree.insert [Ord α] (a : α) : Tree α → Tree α
  | .leaf => .node a .leaf .leaf
  | .node a' lst rst => match compare a a' with
      | .lt => .node a' (lst.insert a) rst
      | .eq => .node a' lst rst
      | .gt => .node a' lst (rst.insert a)

def Tree.linear_contains [BEq α] (a : α) : Tree α → Bool
  | .leaf => false
  | .node a' lst rst => a == a' || lst.linear_contains a || rst.linear_contains a

def Tree.contains [Ord α] (a : α) : Tree α → Bool
  | .leaf => false
  | .node a' lst rst => match compare a a' with
      | .lt => lst.contains a
      | .eq => true
      | .gt => rst.contains a

inductive TreeElem (a : α) : Tree α → Prop where
  | node_here : TreeElem a (.node a lst rst)
  | node_left : TreeElem a lst → TreeElem a (.node a' lst rst)
  | node_right : TreeElem a rst → TreeElem a (.node a' lst rst)

instance : Membership α (Tree α) where
  mem t a := TreeElem a t

def ex_tree : Tree ℕ := .node 1 .leaf .leaf
example : 1 ∈ ex_tree := by
  apply TreeElem.node_here

inductive WithBounds (α : Type) where
  | min
  | el (a : α)
  | max

instance [Ord α] : Ord (WithBounds α) where
  compare x y := match x, y with
    | .min, .min => .eq
    | .max, .max => .eq
    | .min, _ => .lt
    | .max, _ => .gt
    | _, .min => .gt
    | _, .max => .lt
    | .el al, .el ar => compare al ar

instance [BEq α] [Ord α] : BEq (WithBounds α) where
  beq x y := compare x y == .eq

inductive WithBounds.LessThan [LT α] : WithBounds α → WithBounds α → Prop where
  | min_el : LessThan .min (.el a)
  | min_max : LessThan .min .max
  | el_preserved : a < a' → LessThan (.el a) (.el a')
  | el_max : LessThan (.el a) .max

instance [LT α] : LT (WithBounds α) where
  lt := WithBounds.LessThan

def between [LT α] low (a : α) upp := low < WithBounds.el a ∧ WithBounds.el a < upp

inductive BSTNode [LT α] : WithBounds α → WithBounds α → Tree α → Prop where
  | leaf : BSTNode low upp .leaf
  | node : BSTNode low (.el a) lst → BSTNode (.el a) upp rst
          → between low a upp
          → BSTNode low upp (.node a lst rst)

def BST [LT α] (t : Tree α) : Prop := BSTNode .min .max t

variable {α : Type} [ValidElemType α]

theorem linear_contains_finds_if_present
    (a : α) (t : Tree α) : a ∈ t → t.linear_contains a = true := by
  intro Hin
  induction Hin with
  | node_here =>
      unfold Tree.linear_contains
      rewrite [ValidElemType.beq_correct]
      simp
  | node_left Hinl lIH =>
      unfold Tree.linear_contains
      rewrite [lIH]
      simp
  | node_right => sorry

theorem contains_finds_if_present_helper
    {a : α} {t : Tree α} (tv : BSTNode low upp t)
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
    (a : α) (t : Tree α) (tv : BST t)
    : a ∈ t → t.contains a = true := by
  apply (contains_finds_if_present_helper tv)
  repeat constructor


end Lecture
