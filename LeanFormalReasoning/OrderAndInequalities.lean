import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

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
    intro h
    -- let's prove by contradiction, using the add_preserves_le lemma we just proved
    -- h' : ¬ b < c
    by_contra hnp
    -- we can rewrite this as b ≥ c
    -- have tactic: introduce a new, temporary goal. basically proving a "local lemma" within a broader proof
    have h' : c ≤ b := Nat.not_lt.mp hnp
    -- now we can apply the add_preserves_le lemma to get a contradiction
    have h'' : c + a ≤ b + a := add_preserves_le c b a h'
    -- massaging the goal to get a contradiction
    have h''' : a + c ≤ a + b := by
        rw[Nat.add_comm] at h''
        nth_rewrite 2[Nat.add_comm] at h''
        exact h''
    -- show that this contradicts the original assumption
    -- specifically, if a + c ≤ a + b, this means not a + b < a + c, which contradicts h
    have h'''' : ¬ a + b < a + c := Nat.not_lt.mpr h'''
    exact h'''' h
