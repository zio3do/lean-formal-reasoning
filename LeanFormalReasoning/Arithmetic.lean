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
     -- in lean 4, le is defined inductively (not as an existential as in NNG), so `use` doesn't apply directly. however, there is a lemma le_iff_exists_add that states:= b ≤ c ↔ ∃ k, b + k = c
    -- we can use this lemma to find such a k
    intro h
    obtain ⟨k, hk⟩ := le_iff_exists_add.mp h -- extract the witness k from the existential statement
    rw[le_iff_exists_add]
    use c * k
    rw [hk]
    rw [Nat.mul_add]
