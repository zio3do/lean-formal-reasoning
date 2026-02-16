import Mathlib.Tactic

/-!
# Advanced Multi-Lemma Proof

This file contains the uniqueness theorem for the division algorithm—a capstone result
requiring coordinated reasoning across arithmetic, order theory, and propositional logic.
The proof demonstrates structured decomposition into manageable subgoals, explicit
case analysis by contradiction, and manual manipulation of inequalities without
relying on automated decision procedures.

This theorem showcases proof engineering at scale: organizing complex invariants,
managing multiple hypotheses, and building transparent arguments through explicit lemma invocation.
-/

/-! ## Division Algorithm Uniqueness -/

/--
If `n = d*q + r` and `n = d*q' + r'` with both remainders less than `d`,
then the quotients and remainders must be identical.

Proof structure:
1. Establish `q = q'` by contradiction via case analysis
2. Use this to derive `r = r'` by direct cancellation

This is a prime example of multi-step reasoning coordinating arithmetic bounds,
inequality manipulation, and logical case splitting.
-/
theorem div_mod_unique (n d q r q' r' : Nat)
  (hd : d > 0)
  (h1 : n = d*q + r) (hr : r < d)
  (h2 : n = d*q' + r') (hr' : r' < d) :
  q = q' ∧ r = r' := by
  -- First prove q = q' as a lemma we'll use later
  have hq : q = q' := by
    -- Prove by contradiction and case analysis
    by_contra hne
    -- Either q < q' or q' < q
    rcases Nat.lt_or_gt_of_ne hne with (hlt | hgt)
    · -- Case 1: q < q' leads to r ≥ d, contradicting hr : r < d
      -- From q < q', we get q + 1 ≤ q'
      have h_succ : q + 1 ≤ q' := Nat.succ_le_of_lt hlt
      -- Multiply both sides by d: d * (q + 1) ≤ d * q'
      have h_mul : d * (q + 1) ≤ d * q' := Nat.mul_le_mul_left d h_succ
      -- Expand: d * q + d ≤ d * q'
      rw [Nat.mul_add] at h_mul
      rw [Nat.mul_one] at h_mul
      -- Add r' to both sides: d * q + d + r' ≤ d * q' + r'
      have h_lower : d * q + d + r' ≤ d * q' + r' :=
        Nat.add_le_add_right h_mul r'
      -- Substitute n using h2
      rw [← h2] at h_lower
      -- Substitute n using h1
      rw [h1] at h_lower
      -- Now we have: d * q + d + r' ≤ d * q + r
      -- Regroup to prepare for cancellation: d * q + (d + r') ≤ d * q + r
      rw [Nat.add_assoc] at h_lower
      -- Cancel d * q to get: d + r' ≤ r
      have h_cancel : d + r' ≤ r := Nat.le_of_add_le_add_left h_lower
      -- Since r' is a natural number, d ≤ d + r'
      have h_d_le : d ≤ d + r' := Nat.le_add_right d r'
      -- By transitivity: d ≤ r
      have h_d_le_r : d ≤ r := Nat.le_trans h_d_le h_cancel
      -- But hr says r < d, which is ¬(d ≤ r)
      have h_not : ¬(d ≤ r) := Nat.not_le.mpr hr
      -- Contradiction
      exact h_not h_d_le_r

    · -- Case 2: q' < q (symmetric argument)
      -- From q' < q, we get q' + 1 ≤ q
      have h_succ : q' + 1 ≤ q := Nat.succ_le_of_lt hgt
      -- Multiply both sides by d
      have h_mul : d * (q' + 1) ≤ d * q := Nat.mul_le_mul_left d h_succ
      -- Expand: d * q' + d ≤ d * q
      rw [Nat.mul_add] at h_mul
      rw [Nat.mul_one] at h_mul
      -- Add r to both sides: d * q' + d + r ≤ d * q + r
      have h_lower : d * q' + d + r ≤ d * q + r :=
        Nat.add_le_add_right h_mul r
      -- Substitute n using h1 and h2
      rw [← h1] at h_lower
      rw [h2] at h_lower
      -- Now we have: d * q' + d + r ≤ d * q' + r'
      -- Regroup to prepare for cancellation: d * q' + (d + r) ≤ d * q' + r'
      rw [Nat.add_assoc] at h_lower
      -- Cancel d * q' to get: d + r ≤ r'
      have h_cancel : d + r ≤ r' := Nat.le_of_add_le_add_left h_lower
      -- Since r is a natural number, d ≤ d + r
      have h_d_le : d ≤ d + r := Nat.le_add_right d r
      -- By transitivity: d ≤ r'
      have h_d_le_r' : d ≤ r' := Nat.le_trans h_d_le h_cancel
      -- But hr' says r' < d, which is ¬(d ≤ r')
      have h_not : ¬(d ≤ r') := Nat.not_le.mpr hr'
      -- Contradiction
      exact h_not h_d_le_r'

  -- Now construct the conjunction
  constructor
  · -- Part A: q = q'
    exact hq

  · -- Part B: Prove r = r' by substituting q = q' and canceling
    -- Combining h1 and h2 with q = q'
    have h_eq : d * q + r = d * q + r' := by
      calc d * q + r = n := h1.symm
           _ = d * q' + r' := h2
           _ = d * q + r' := by rw [← hq]
    -- Cancel d * q from both sides
    exact Nat.add_left_cancel h_eq
