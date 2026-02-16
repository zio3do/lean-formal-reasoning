import Mathlib.Data.Nat.Basic
import LeanFormalReasoning.Arithmetic

-- 2.3 Divisibility under Addition
-- first existential proof; must construct witnesses
theorem my_dvd_add {a b c : Nat} : a ∣ b → a ∣ c → a ∣ b + c := by
    -- proof
    intro h1 h2
    cases h1 with
    | intro k hk =>
    cases h2 with
    | intro m hm =>
    use k + m
    rw [hk, hm]
    rw [← Nat.mul_add]

-- 2.4 Parity via Divisibility
theorem even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
    -- proof
    induction n with
    | zero =>
    left
    use 0
    | succ n ih =>
    cases ih with
    | inl h =>
    right
    apply Exists.elim h
    intro k hk
    use k
    rw [hk]
    | inr h =>
    left
    apply Exists.elim h
    intro k hk
    use k + 1
    rw [hk]
    rw [Nat.mul_add]
