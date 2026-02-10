import Mathlib.Tactic


--  2.2 Order Preservation under Addition
theorem add_preserves_le (a b c : Nat) : a ≤ b → a + c ≤ b + c := by
    -- proof
    intro h
    induction c with
    | zero =>
    repeat rw[Nat.add_zero]
    exact h
    | succ d hd =>
    -- succ_le_succ, le_trans
    repeat rw[Nat.add_succ]
    apply Nat.succ_le_succ at hd
    exact hd


-- 2.5 Strict Inequality Preservation under Addition
 -- could require previous lemmas (e.g. T2.2)
theorem my_lt_of_add_lt_add_left (a b c : Nat) : a + b < a + c → b < c := by
    -- proof
    sorry
