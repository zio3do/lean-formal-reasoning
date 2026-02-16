import Mathlib.Data.Nat.Basic
import LeanFormalReasoning.Arithmetic

/-!
# Number-Theoretic Properties

This file establishes divisibility and parity results through explicit witness construction.
Theorems demonstrate existential reasoning patterns including case analysis on existential
hypotheses and induction with disjunctive goals. The proofs avoid automation to maintain
transparency in witness manipulation and case handling.

Key theorems include closure of divisibility under addition and the fundamental
parity dichotomy for natural numbers.
-/

/-! ## Divisibility -/

/--
Divisibility is preserved under addition.
If `a | b` and `a | c`, then `a | (b + c)`.
Proved by extracting and recombining witnesses.
-/
theorem my_dvd_add {a b c : Nat} : a ∣ b → a ∣ c → a ∣ b + c := by
  intro h1 h2
  cases h1 with
  | intro k hk =>
    cases h2 with
    | intro m hm =>
      use k + m
      rw [hk, hm, ← Nat.mul_add]

/-! ## Parity -/

/--
Every natural number is either even or odd.
Proved by induction with alternating case construction.
-/
theorem even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero =>
    left
    use 0
  | succ n ih =>
    -- Successor alternates: even → odd, odd → even
    cases ih with
    | inl h =>
      -- n is even, so succ n is odd
      right
      apply Exists.elim h
      intro k hk
      use k
      rw [hk]
    | inr h =>
      -- n is odd, so succ n is even
      left
      apply Exists.elim h
      intro k hk
      use k + 1
      rw [hk, Nat.mul_add]
