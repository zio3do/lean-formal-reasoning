import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-!
# Order and Inequality Reasoning

This file develops preservation and cancellation properties for inequalities.
Theorems demonstrate both direct inductive proofs and proof by contradiction.
The strict inequality cancellation theorem showcases multi-step reasoning involving
conversion between strict and non-strict orderings.

These results are essential for reasoning about monotonicity and bounds in
more complex mathematical arguments.
-/

/-! ## Order Preservation -/

/--
Addition preserves non-strict inequality on the right.
Proved by induction on the added value.
-/
theorem add_preserves_le (a b c : Nat) : a ≤ b → a + c ≤ b + c := by
  intro h
  induction c with
  | zero =>
    repeat rw [Nat.add_zero]
    exact h
  | succ d hd =>
    repeat rw [Nat.add_succ]
    apply Nat.succ_le_succ at hd
    exact hd

/-! ## Cancellation for Strict Inequality -/

/--
Left cancellation for strict inequality under addition.
Strategy: proof by contradiction using the contrapositive and order reflection.
-/
theorem my_lt_of_add_lt_add_left (a b c : Nat) : a + b < a + c → b < c := by
  intro h
  by_contra hnp
  -- Convert ¬(b < c) to c ≤ b
  have h' : c ≤ b := Nat.not_lt.mp hnp
  -- Apply order preservation
  have h'' : c + a ≤ b + a := add_preserves_le c b a h'
  -- Rearrange via commutativity
  have h''' : a + c ≤ a + b := by
    rw [Nat.add_comm] at h''
    nth_rewrite 2 [Nat.add_comm] at h''
    exact h''
  -- Derive contradiction
  have h'''' : ¬ a + b < a + c := Nat.not_lt.mpr h'''
  exact h'''' h
