import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- 2.1 Additive Cancellation
-- NNG: Advanced Addition WOrld Level 2/6
theorem my_add_left_cancel (a b c : Nat) : a + b = a + c → b = c := by
    -- proof
    induction a with
    | zero =>
    repeat rw[Nat.zero_add]
    intro h
    exact h
    -- exact id -- id is the identity function
    | succ a ih =>
    -- Target: massage goal into ih via succ tactics
    repeat rw[← Nat.succ_eq_add_one]
    repeat rw [Nat.succ_add]
    rw[Nat.succ_inj]
    exact ih


-- 2.7 Monotonicity of Multiplication
-- involves nested induction + multi-lemme orchestration
theorem my_mul_le_mul_left (a b c : Nat) : a ≤ b → c * a ≤ c * b := by
    -- proof
    sorry

-- get AI to critique my proofs after finishing
