import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma

namespace MockExam

inductive BinTree α where
  | leaf (a : α)
  | node (lst rst : BinTree α)

def BinTree.map (f : α → β) : BinTree α → BinTree β
  | .leaf a => .leaf (f a)
  | .node lst rst => .node (lst.map f) (rst.map f)

theorem BinTree.map_id {t : BinTree α} : t.map id = t := by
  induction t with
  | leaf a =>
      unfold BinTree.map
      unfold id
      rfl
  | node lst rst lih rih =>
      unfold BinTree.map
      rewrite [lih, rih]
      rfl

def BinTree.fold (leafFun : α → β) (nodeFun : BinTree α → β → BinTree α → β → β) : BinTree α → β
  | .leaf n => leafFun n
  | .node lhs rhs => nodeFun lhs (lhs.fold leafFun nodeFun) rhs (rhs.fold leafFun nodeFun)

def BinTree.height : BinTree α → ℕ := fold sorry sorry

-- `Balanced tree n` states that `tree` is a balanced tree of height `n`.
-- That is, the distance from the root to each leaf is either `n` or `n-1`.
-- (We need to allow the latter case to support trees whose number of leaves is not a power of two.)
inductive Balanced : BinTree α → ℕ → Prop where
  | leaf_zero : Balanced (.leaf a) 0
  | leaf_one : Balanced (.leaf a) 1
  | node : Balanced lst k → Balanced rst k → Balanced (.node lst rst) (k+1)

theorem balanced_bounds_height (tree : BinTree α) (balanced : Balanced tree n) : tree.height ≤ n := by sorry

end MockExam
