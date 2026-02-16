import Mathlib.Tactic

/-!
# Foundational Arithmetic

This file establishes core algebraic properties through explicit induction.
Theorems include associativity of addition, distributivity of multiplication over addition,
and multiplication by successors. All proofs avoid automation to demonstrate manual
constructions of inductive arguments on natural numbers.

This serves as the foundation for more complex reasoning in later files.
-/

/-! ## Associativity and Distributivity -/

/--
Associativity of addition on natural numbers.
Proved by induction on the third argument.
-/
theorem my_add_assoc (m n k : Nat) : m + (n + k) = (m + n) + k := by
  induction k with
  | zero =>
    repeat rw [Nat.add_zero]
  | succ k ih =>
    repeat rw [Nat.add_succ]
    rw [ih]

/--
Right distributivity of multiplication over addition.
Demonstrates nested rewriting with an induction hypothesis.
-/
theorem my_mul_add (m n k : Nat) : m * (n + k) = m * n + m * k := by
  induction k with
  | zero =>
    rw [Nat.mul_zero]
    repeat rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_succ]
    repeat rw [Nat.mul_succ]
    rw [ih, my_add_assoc]

/-! ## Multiplication Identities -/

/--
Expanding (n + 1) * m using distributivity and commutativity.
-/
theorem plus_one_mul (n m : Nat) : (n + 1) * m = n * m + m := by
  nth_rewrite 1 [Nat.mul_comm]
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
