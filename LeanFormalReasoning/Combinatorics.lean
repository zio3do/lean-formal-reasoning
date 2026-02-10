import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic -- the operators are separate modules from the datatypes
import Mathlib.Data.Finset.Range

-- 2.6 Finite Sum Identity
open Finset

-- bridges to combinatorics and contest math; also a good example of using the library
theorem sum_range_id (n : Nat) :
  (range (n+1)).sum id = n*(n+1)/2 := by
  -- proof
  induction n with
  | zero =>
    simp -- sum over empty set is 0, and RHS is 0
  | succ n ih =>
    -- sum over range (n+1) is sum over range n plus n
    rw [Finset.sum_range_succ]

    -- need to show n is not in range n
    -- rw [Finset.sum_range_succ]
    -- need to show n is not in range n
    rw [Finset.mem_range (n+1)]
    simp
