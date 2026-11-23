import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# My first Lean project

This module contains a proof that two plus two equals four.
-/

-- First mathematical proof
theorem nat_two_add_two_eq_four :
    2 + 2 = 4 := by
  norm_num
