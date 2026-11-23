import Mathlib.Data.Nat.Basic

set_option linter.style.header false

/-!
# Commutativity of natural number addition

A proof by induction on the second argument.
-/

theorem nat_add_comm_induction (n m : Nat) : n + m = m + n := by
  induction m with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
  | succ k ih =>
    rw [Nat.add_succ, ih, Nat.succ_add]
