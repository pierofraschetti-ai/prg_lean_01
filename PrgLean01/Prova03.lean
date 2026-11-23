import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Elementary number theory exercises

Guided exercises on natural numbers, in increasing order of difficulty.
Replace each `sorry` with a proof, one at a time, recompiling after each one.
When you are done, check each theorem with `#print axioms`: it must not depend on `sorryAx`.

Useful tactics: `obtain`, `use`, `ring`, `omega`, `simp`, `rcases`, `induction`,
`by_contra`, `push Not`, `exact`.
-/

namespace Prova03

/-! ## Exercise 1: divisibility -/

-- `a ∣ b` means `∃ k, b = a * k`.
-- Hint: `obtain ⟨k, rfl⟩ := h1` unpacks the hypothesis and substitutes `b`.
-- Then provide the witness with `exact ⟨_, by ring⟩` (which number works?).
-- Alternative: the Mathlib lemma `dvd_add` solves it in one step.
theorem dvd_add_of_dvd (a b c : ℕ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  sorry

/-! ## Exercise 2: even numbers -/

-- `Even n` means `∃ r, n = r + r`.
-- Hint: unpack `h` with `obtain ⟨k, rfl⟩ := h`, then `(k + k) ^ 2 = ? + ?`.
theorem even_sq_of_even (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  sorry

/-! ## Exercise 3: product of consecutive numbers -/

-- Hint: split into cases with
--   `rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩`
-- (`Odd n` means `∃ k, n = 2 * k + 1`). In each case find the witness and close with `ring`.
theorem even_mul_succ (n : ℕ) : Even (n * (n + 1)) := by
  sorry

/-! ## Exercise 4: Gauss's sum -/

-- 2 * (0 + 1 + ... + n) = n * (n + 1).
-- Hint: induction on `n`, as in `Prova02`.
-- * `zero` case: `simp`.
-- * `succ` case: `rw [Finset.sum_range_succ, mul_add, ih]`, then `ring`.
theorem gauss_sum (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  sorry

/-! ## Exercise 5: consecutive numbers are coprime -/

-- Skeleton: close the `sorry`s one at a time.
-- Useful lemmas: `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`,
-- `Nat.dvd_add_right : a ∣ b → (a ∣ b + c ↔ a ∣ c)`, `Nat.dvd_one : n ∣ 1 ↔ n = 1`.
theorem coprime_succ (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  have h1 : Nat.gcd n (n + 1) ∣ n := by sorry
  have h2 : Nat.gcd n (n + 1) ∣ n + 1 := by sorry
  have h : Nat.gcd n (n + 1) ∣ 1 := by sorry
  sorry

/-! ## Exercise 6: there are infinitely many primes (Euclid) -/

-- Idea: the smallest prime factor `p` of `n! + 1` cannot be `< n`,
-- otherwise it would divide both `n!` and `n! + 1`, hence `1`.
-- Useful lemmas: `Nat.factorial_pos`, `Nat.minFac_prime : n ≠ 1 → Nat.Prime n.minFac`,
-- `Nat.minFac_dvd`, `Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n.factorial`,
-- `Nat.Prime.pos`, `Nat.Prime.ne_one`, `Nat.dvd_add_right`, `Nat.dvd_one`.
theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let m := n.factorial + 1
  let p := Nat.minFac m
  have hm : m ≠ 1 := by sorry
  have hp : Nat.Prime p := by sorry
  have hdvd : p ∣ m := by sorry
  have hle : n ≤ p := by
    by_contra hlt
    push Not at hlt
    have h1 : p ∣ n.factorial := by sorry
    have h2 : p ∣ 1 := by sorry
    sorry
  sorry

end Prova03
