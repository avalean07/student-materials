import Mathlib.Tactic.Linarith
import FunctionalProgramming.Direction
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

def RBTree.size : RBTree α c k → ℕ
  | .leaf => 0
  | .red_node _ lst rst => 1 + lst.size + rst.size
  | .black_node _ lst rst => 1 + lst.size + rst.size

--
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
--

-- inductive Direction where | left | right

def BinTree.find_insertion_ancestry (ai : α) : BinTree α → List (α × Direction × BinTree α) → Option (List (α × Direction × BinTree α))
  | .leaf, acc => some acc
  | .node a lst rst, acc  => match compare ai a with
      | .lt => lst.find_insertion_ancestry ai (⟨ a, .left, rst ⟩ :: acc)
      | .eq => none
      | .gt => rst.find_insertion_ancestry ai (⟨ a, .right, lst ⟩ :: acc)

def BinTree.rebuild_from_ancestry (inode : BinTree α) : List (α × Direction × BinTree α) → BinTree α
  | [] => inode
  | ⟨ a , .left , t ⟩ :: anc => (BinTree.node a inode t).rebuild_from_ancestry anc
  | ⟨ a , .right , t ⟩ :: anc => (BinTree.node a t inode).rebuild_from_ancestry anc

def BinTree.insert (ai : α) (t : BinTree α) : BinTree α :=
  match t.find_insertion_ancestry ai [] with
  | none => t
  | some anc => (BinTree.node ai .leaf .leaf).rebuild_from_ancestry anc

-- Helper function to test our insertion.
def iterate (f : ℕ → β → β) (init : β) : ℕ → List β
  | .zero => [init]
  | .succ k => init :: iterate f (f k init) k

def BinTree.toList : BinTree α → List α
  | .leaf => []
  | .node a lst rst => lst.toList ++ [a] ++ rst.toList

def emptyTree : BinTree ℕ := .leaf
#eval forM ((iterate (fun k m => m.insert k) emptyTree 5).map (·.toList)) IO.println

--
-- Insertion into red-black trees.
--

namespace Try1
-- We build the ancestry up top-to-bottom.
-- At each point, we have one node "missing" from the tree.
-- Initially, this is the whole tree missing (`.root`); when we add nodes, we build up the structure
-- of the tree above the missing node.
--
-- `Ancestry α c k h` is a tree of black depth `h` with an `RBTree α c k` missing,
-- Note that the root node is always black, as we assumed earlier.
inductive Ancestry (α : Type) : Color → ℕ → ℕ → Type where
  -- If the whole tree is missing, the black depth of the whole tree is the same as the black depth of the missing tree.
  | root : Ancestry α .black k k
  -- Given an ancestry where the missing node is red, we can extend it with a red node.
  -- The new missing node and the sibling of the missing node both have to be black.
  | child_of_red (dir : Direction) (pa : α) (sib : RBTree α .black k) : Ancestry α .red k h → Ancestry α .black k h
  -- Given an ancestry where the missing node is black, we can extend with a black node,
  -- provided the black depth of the missing node is at least 1.
  -- The remaining black depth is reduced by one.
  | child_of_black (dir : Direction) (pa : α) (sib : RBTree α sc k) : Ancestry α .black (k+1) h → Ancestry α c k h

-- Whenever we expect a red node, we can also provide a black node instead.
def Ancestry.color_expected_node_black : Ancestry α .red k h → Ancestry α .black k h
  | .child_of_black dir pa sib anc => .child_of_black dir pa sib anc

inductive InsertionPoint (α : Type) (h : ℕ) where
  | insert_at : Ancestry α c 0 h → InsertionPoint α h
  | already_present : InsertionPoint α h
end Try1
open Try1

mutual
  def RBTree.find_black_node_insertion_point (anc : Ancestry α .black k h) (ai : α) :
      RBTree α .black k → InsertionPoint α h
    | .leaf => .insert_at anc
    | .black_node a lst rst => match compare ai a with
        | .lt => lst.find_after_black_node_insertion_point (.child_of_black .left a rst anc) ai
        | .eq => .already_present
        | .gt => rst.find_after_black_node_insertion_point (.child_of_black .right a lst anc) ai

  def RBTree.find_after_black_node_insertion_point (anc : Ancestry α c k h) (ai : α) :
      RBTree α c k → InsertionPoint α h := match c with
        | .black => RBTree.find_black_node_insertion_point anc ai
        | .red => fun
          | .red_node a lst rst => match compare ai a with
              | .lt => lst.find_black_node_insertion_point (.child_of_red .left a rst anc) ai
              | .eq => .already_present
              | .gt => rst.find_black_node_insertion_point (.child_of_red .right a lst anc) ai
end

def RootedRBTree.find_root_insertion_point (ai : α) (rt : RootedRBTree α k) : InsertionPoint α k :=
  rt.find_black_node_insertion_point .root ai

structure AnyHeightRBTree (α : Type) : Type where
  height : ℕ
  tree : RBTree α .black height

def RBTree.insert (ai : α) (rt : RootedRBTree α k) : AnyHeightRBTree α :=
  match rt.find_root_insertion_point ai with
  | .insert_at anc => sorry -- next time.
  | .already_present => ⟨ _ , rt ⟩
