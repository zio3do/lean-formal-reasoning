import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic -- the operators are separate modules from the datatypes
import Mathlib.Data.Finset.Range


-- Use the fact that if 2*a = 2*b, then a = b (cancellation property)
theorem eq_of_mul_eq_mul_right (a b : Nat) : 2 * a = 2 * b → a = b := by
  intro h
  -- Use the fact that 0 < 2 to cancel the multiplication
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h


-- 2.6 Finite Sum Identity
open Finset

-- bridges to combinatorics and contest math; also a good example of using the library
theorem sum_range_id (n : Nat) :
  (range (n+1)).sum id = n*(n+1)/2 := by
  -- why n+1? because range in Lean is EXCLUSIVE
  -- proof
  induction n with
  | zero =>
    simp -- sum over empty set is 0, and RHS is 0
  | succ n ih =>
    -- sum over range (n+2) equals sum over range (n+1) plus (n+1)

    -- algebraic manipulation to get the desired form
    -- 1) multiply both sides by 2 to clear the denominator
         -- instead of succ_inj, we need like a "mul_eq_mul_right" or something to show that we can multiply both sides by 2 without changing the equality
    have h0 : 2 * ((n * (n + 1)) / 2 + (n + 1)) = 2 * (n * (n + 1) / 2) + 2 * (n + 1) := by
      rw[Nat.mul_add]
    have h1 : 2*(n*(n+1) / 2) = n*(n+1) := by
      sorry
    have h2 : 2 * ((n * (n + 1)) / 2 + (n + 1)) = n*(n+1) + 2*(n+1) := by
      rw[Nat.mul_add]
      rw[h1]
    have h3 : n*(n+1) + 2*(n+1) = (n + 1) * (n + 2) := by
      rw[← Nat.right_distrib]
      rw[Nat.mul_comm]
    have h4 : 2 * ((n * (n + 1)) / 2 + (n + 1)) = (n + 1) * (n + 2) := by
      rw[h2]
      rw[h3]
    have h5 : 2 * ((n + 1) * (n + 1 + 1) / 2) = (n + 1) * (n + 1 + 1) := by
      rw[← Nat.mul_div_assoc]
      rw[Nat.mul_div_cancel_left]
      decide


    rw [Finset.sum_range_succ]
    rw[ih]
    simp
    apply eq_of_mul_eq_mul_right
    rw[h4]
    rw[h5]
    -- now, massage the RHS
    --  distribute the 2* on the RHS










    -- 2) simplify both sides
    -- CURRENT: how to show that multiplying 2 cancels division by 2?
    -- have h3 : n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2) := by
    --   simp at h1

    -- have even1 : 2 ∣ n * (n + 1) := Nat.even_mul_succ_self n
    -- have even2 : 2 ∣ (n + 1) * (n + 2) := by
    --   rw [Nat.mul_comm]; exact Nat.even_mul_succ_self (n + 1)
    -- -- Cancel the 2's using the divisibility facts
    -- exact Nat.eq_div_of_mul_eq_some even1 even2 h1






-- theorem mul_div_cancel_two (n : Nat) : (n * 2) / 2 = n :=
--   Nat.mul_div_cancel n (by decide)
