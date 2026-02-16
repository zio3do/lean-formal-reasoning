import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-!
# Arithmetic Reasoning

This file develops cancellation properties and monotonicity results for natural number arithmetic.
Key techniques include induction, existential extraction via `obtain`, and proof by contradiction.
The theorems demonstrate working with inequality structures and converting between different
representations of ordering (inductive vs. existential).

These results are foundational for inequality reasoning in more advanced contexts.
-/

/-! ## Cancellation -/

/--
Left cancellation for addition: if `a + b = a + c`, then `b = c`.
Proved by induction on `a` using the `succ_inj` property.
-/
theorem my_add_left_cancel (a b c : Nat) : a + b = a + c → b = c := by
  induction a with
  | zero =>
    repeat rw [Nat.zero_add]
    intro h
    exact h
  | succ a ih =>
    repeat rw [← Nat.succ_eq_add_one]
    repeat rw [Nat.succ_add]
    rw [Nat.succ_inj]
    exact ih

/-! ## Monotonicity -/

/--
Multiplication preserves inequality: if `a ≤ b`, then `c * a ≤ c * b`.
Strategy: convert inequality to existential form, multiply the witness, and reconstruct.
-/
theorem my_mul_le_mul_left (a b c : Nat) : a ≤ b → c * a ≤ c * b := by
  intro h
  -- Convert a ≤ b to existential: ∃ k, b = a + k
  obtain ⟨k, hk⟩ := le_iff_exists_add.mp h
  rw [le_iff_exists_add]
  -- Witness is c * k
  use c * k
  rw [hk, Nat.mul_add]
