import Mathlib.Tactic.Linarith
import FunctionalProgramming.WithBounds

--
-- Some relevant material from the last lecture.
--

inductive BinTree (α : Type) where
  | leaf
  | node (a : α) (lst rst : BinTree α)
  deriving Repr

-- Instead of ValidElemType, we will use the standard type LinearOrder.
variable {α : Type} [LinearOrder α]

inductive BSTNode : WithBounds α → WithBounds α → BinTree α → Prop where
  | leaf : BSTNode low upp .leaf
  | node : BSTNode low (.el a) lst → BSTNode (.el a) upp rst
          → between low a upp
          → BSTNode low upp (.node a lst rst)

def BST (t : BinTree α) : Prop := BSTNode .min .max t

--
-- Definition of a red-black tree
--

/-
1. Every node is red or black.
2. The root is black.
3. The leaves are black.
4. Every red node has only black children.
5. For every node, all its paths to its leaves have the same number of black nodes.
-/

inductive Color where | red | black deriving Repr

-- `RBTree α c k` is a red-black (sub)tree with a root of color `c` and a black depth of `k`.
inductive RBTree (α : Type) : Color → ℕ → Type where
  | leaf : RBTree α .black 0
  | red_node (a : α) (lst rst : RBTree α .black k) : RBTree α .red k
  | black_node (a : α) (lst : RBTree α lc k) (rst : RBTree α rc k) : RBTree α .black (k+1)

-- A rooted red-black tree is just one where the root is black.
def RootedRBTree α := RBTree α .black

def RBTree.to_BinTree : RBTree α c k → BinTree α
  | .leaf => .leaf
  | .red_node a lst rst => .node a lst.to_BinTree rst.to_BinTree
  | .black_node a lst rst => .node a lst.to_BinTree rst.to_BinTree

/---
-- Insertion into binary trees via "ancestries"
-- I call this an ancestry because it stores the data on ancestors in the tree;
-- the standard term is a zipper.
-- See also: https://strictlypositive.org/diff.pdf
--
-- Strategy for inserting ai into t
-- 1. Find where we are ai
--   Track the parts of the tree that we *didn't* recurse into.
-- 2. Create a red node there
-- 3. Bubble the issues up to the root
--   Reassemble tree from the parts we "cut off"
--/

inductive Direction where | left | right
  deriving Ord, BEq

inductive Ancestry (α : Type) : Color → ℕ → ℕ → Type where
  | root : Ancestry α .black k k
  | red_parent :
      Direction → α → RBTree α .black k →
      Ancestry α .red k h → Ancestry α .black k h
  | black_parent :
      Direction → α → RBTree α cs k →
      Ancestry α .black (k+1) h → Ancestry α c k h

def RBTree.reverse : RBTree α c k → RBTree α c k := sorry
def Direction.order (node : RBTree α c k) : Direction → RBTree α c k := sorry

def Direction.maybeFlip (f : α → α → β) (a1 a2 : α) : Direction → β
  | .left => f a1 a2
  | .right => f a2 a1

def Ancestry.rebuild_from_ancestry (node : RBTree α c k) :
    Ancestry α c k h → RBTree α .black h
  | .root => node
  | .red_parent dir a sib anc =>
      anc.rebuild_from_ancestry (dir.order (.red_node a node sib))
  | .black_parent dir a sib anc =>
      anc.rebuild_from_ancestry (dir.order (.black_node a node sib))

def RBTree.color_black : RBTree α .red k → RBTree α .black k := sorry

def Ancestry.insert_new (node : RBTree α .red k) :
    Ancestry α c k h → Σ h', RBTree α .black h'
  | .root => ⟨ _, node.color_black ⟩
  | .red_parent dir a sib anc => match anc with
      | .black_parent gdir ga unc anc' =>
          if dir = gdir
          then
            let lst := node.color_black
            let rst := gdir.order (.black_node ga sib unc)
            anc'.insert_new (dir.order (.red_node a lst rst))
          else
            sorry
  | .black_parent dir a sib anc =>
      ⟨ _, anc.rebuild_from_ancestry (dir.order (.black_node a node sib)) ⟩
