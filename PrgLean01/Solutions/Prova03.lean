import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Solutions to the exercises in `PrgLean01.Prova03`

Try the exercises on your own before reading these solutions.
-/

namespace Prova03.Solutions

theorem dvd_add_of_dvd (a b c : ℕ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨k + l, by ring⟩

theorem even_sq_of_even (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k ^ 2, by ring⟩

theorem even_mul_succ (n : ℕ) : Even (n * (n + 1)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (k + k + 1), by ring⟩
  · exact ⟨(2 * k + 1) * (k + 1), by ring⟩

theorem gauss_sum (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem coprime_succ (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  have h : Nat.gcd n (n + 1) ∣ 1 := by
    have h1 : Nat.gcd n (n + 1) ∣ n := Nat.gcd_dvd_left n (n + 1)
    have h2 : Nat.gcd n (n + 1) ∣ n + 1 := Nat.gcd_dvd_right n (n + 1)
    exact (Nat.dvd_add_right h1).mp h2
  exact Nat.dvd_one.mp h

theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let m := n.factorial + 1
  let p := Nat.minFac m
  have hm : m ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  have hp : Nat.Prime p := Nat.minFac_prime hm
  have hdvd : p ∣ m := Nat.minFac_dvd m
  have hle : n ≤ p := by
    by_contra hlt
    push Not at hlt
    have h1 : p ∣ n.factorial := Nat.dvd_factorial hp.pos hlt.le
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    exact hp.ne_one (Nat.dvd_one.mp h2)
  exact ⟨p, hle, hp⟩

end Prova03.Solutions
