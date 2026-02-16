import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

open Finset

-- Helper lemma: product of consecutive integers is always even
lemma two_dvd_prod_succ (n : Nat) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = 2k, so n * (n+1) = 2k * (2k+1)
    use k * (2 * k + 1)
    ring
  · -- n = 2k+1, so n * (n+1) = (2k+1) * (2k+2) = (2k+1) * 2(k+1)
    use (2 * k + 1) * (k + 1)
    ring

-- Main theorem: sum of first n natural numbers
theorem sum_range_id (n : Nat) :
  (range (n+1)).sum id = n*(n+1)/2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, id]
    -- Goal: n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2

    -- Both sides need the divisibility lemma to cancel divisions
    have h_div : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
      Nat.mul_div_cancel' (two_dvd_prod_succ n)
    have h_div' : 2 * ((n + 1) * (n + 2) / 2) = (n + 1) * (n + 2) :=
      Nat.mul_div_cancel' (two_dvd_prod_succ (n + 1))

    -- Multiply both sides by 2 to clear denominators
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [h_div']
    rw [Nat.mul_add, h_div]
    ring
