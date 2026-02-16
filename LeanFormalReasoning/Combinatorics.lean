import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

/-!
# Combinatorics: Triangular Number Sum

This file proves the closed-form formula for the sum of natural numbers from 0 to n.
The proof demonstrates handling of natural number division (which truncates), requiring
explicit divisibility arguments to justify algebraic manipulations.

Key challenge: Unlike real-number arithmetic, `(n * (n + 1)) / 2` only equals the expected
value when `2 ∣ n * (n + 1)`, necessitating a helper lemma establishing this divisibility
through even/odd case analysis.
-/

open Finset

/-! ## Helper Lemmas -/

/--
The product of any natural number and its successor is divisible by 2.
Proved by case analysis on parity: if `n` is even, the product contains factor 2;
if `n` is odd, then `n+1` is even.
-/
lemma two_dvd_prod_succ (n : Nat) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = 2k, so n * (n+1) = 2k * (2k+1)
    use k * (2 * k + 1)
    ring
  · -- n = 2k+1, so n * (n+1) = (2k+1) * (2k+2) = (2k+1) * 2(k+1)
    use (2 * k + 1) * (k + 1)
    ring

/-! ## Main Theorem -/

/--
The sum of natural numbers from 0 to n equals n(n+1)/2.

Proof by induction on n. The successor case multiplies both sides by 2 to clear
denominators, then uses divisibility lemmas to justify cancellation. The final
algebraic verification is handled by `ring` after the conceptually difficult
divisibility reasoning is explicit.
-/
theorem sum_range_id (n : Nat) :
  (range (n+1)).sum id = n*(n+1)/2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, id]
    -- Goal: n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2

    -- Establish divisibility to cancel divisions on both sides
    have h_div : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
      Nat.mul_div_cancel' (two_dvd_prod_succ n)
    have h_div' : 2 * ((n + 1) * (n + 2) / 2) = (n + 1) * (n + 2) :=
      Nat.mul_div_cancel' (two_dvd_prod_succ (n + 1))

    -- Multiply both sides by 2 to clear denominators, then verify algebraically
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [h_div']
    rw [Nat.mul_add, h_div]
    ring
