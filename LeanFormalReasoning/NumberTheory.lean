import Mathlib.Data.Nat.Basic
import LeanFormalReasoning.Arithmetic

-- 2.3 Divisibility under Addition
-- first existential proof; must construct witnesses
theorem dvd_add {a b c : Nat} : a ∣ b → a ∣ c → a ∣ b + c := by
    -- proof
    sorry

-- 2.4 Parity via Divisibility
theorem even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
    -- proof
    induction n with
    | zero =>
    left
    use 0
    | succ d hd =>
    cases hd with
    | inl hx =>
    -- how do we work with the witness k in the proof?
    cases hx with
    | intro k hk =>
    right
    use k
    rw [hk]
    | inr hy =>
    cases hy with
