import Mathlib.Tactic.Linarith

namespace Week02

-- These are pairs of very similar statements.
-- In each case, one statement is easy to prove, while the other requires induction.
-- Try to look at the definition of the operations and see whether you can
-- figure out why that is:

--use reduce at, efl, indcution, exact
#print Nat.add
#print Nat.mul

example (n : ℕ) : n + 0 = n := by
rw [add_zero]

example (n : ℕ) : 0 + n = n := by
induction n with
| zero =>
  rw [add_zero]
| succ k ih =>
  rw [Nat.add_succ, ih]

example (n : ℕ) : n * 0 = 0 := by
rw [mul_zero]

example (n : ℕ) : 0 * n = 0 := by
induction n with
| zero =>
  rw [mul_zero]
| succ k ih =>
  rw [Nat.mul_succ, ih, Nat.add_zero]



example (n : ℕ) : n * 1 = n := by
rw [mul_one]

example (n : ℕ) : 1 * n = n := sorry

example (n m : Nat) : n + m = m + n := sorry


-- Define the following functions using recursion:
def length : List α → ℕ := sorry
def reverse : List α → List α := sorry
def minimum : List ℕ → Option ℕ := sorry
def flatten : List (List ℕ) → List ℕ := sorry
def take : ℕ → List α → List α := sorry
def drop : ℕ → List α → List α := sorry

example (xs : List α) : length (reverse xs) = length xs := sorry
example (xs : List ℕ) : minimum (reverse xs) = minimum xs := sorry
example (xs : List ℕ) : reverse (reverse xs) = xs := sorry
example (xs ys : List ℕ) : minimum (xs ++ ys) = (minimum xs).min (minimum ys) := sorry

example (n k : ℕ) (xs : List α) : n ≤ k → take n (take k xs) = take n xs := sorry
example (n k : ℕ) (xs : List α) : drop (n + k) xs = drop n (drop k xs) := sorry

-- You may want to change some of the above examples into theorems to prove this.
example (n k : ℕ) (xs : List α) : drop k (drop n xs) = drop n (drop k xs) := sorry

-- Define an inductive data structure for binary trees and define similar
-- functions for it: size, reverse, minimum, flatten.
-- Prove similar properties for trees.

end Week02
