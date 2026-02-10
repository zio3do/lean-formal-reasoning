import Mathlib.Tactic

-- Associativity of Addition
-- Renamed to avoid conflict with Mathlib's add_assoc
theorem my_add_assoc (m n k : Nat) : m + (n + k) = (m + n) + k := by
    induction k with
    | zero =>
    repeat rw[Nat.add_zero]
    | succ k ih =>
    repeat rw[Nat.add_succ]
    rw[ih]

-- Renamed to avoid conflict with Mathlib's mul_add
theorem my_mul_add (m n k : Nat) : m * (n + k) = m * n + m * k := by
    induction k with
    | zero =>
    rw [Nat.mul_zero]
    repeat rw [Nat.add_zero]
    | succ k ih =>
    rw[Nat.add_succ]
    repeat rw[Nat.mul_succ]
    rw[ih]
    rw[my_add_assoc]

theorem plus_one_mul (n m : Nat) : (n + 1) * m = n * m + m := by
    nth_rewrite 1 [Nat.mul_comm]
    rw [Nat.mul_add]
    rw [Nat.mul_one]
    rw [Nat.mul_comm]
