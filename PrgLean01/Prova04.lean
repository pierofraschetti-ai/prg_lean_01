import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false

/-!
# Fermat's little theorem

If `p` is prime and `p` does not divide `a`, then `a ^ (p - 1) ≡ 1 (mod p)`.

Both hypotheses are necessary; each counterexample below violates exactly one of them:
- `p` prime: for `p = 4` (not prime) and `a = 3` (not divisible by 4) we get
  `3 ^ 3 = 27 ≡ 3 (mod 4)`, not `1`.
- `p ∤ a`: for `p = 3` (prime) and `a = 6` (divisible by 3) we get
  `6 ^ 2 = 36 ≡ 0 (mod 3)`, not `1`.

## Proof strategy

We work in `ZMod p`, the integers modulo `p`, which is a field because `p` is prime.

1. `natCast_pow_prime_eq_self`: for every natural number `a`, `a ^ p = a` in `ZMod p`.
   By induction on `a`, using the "freshman's dream" `(x + y) ^ p = x ^ p + y ^ p`,
   which holds in characteristic `p` (`add_pow_char`).
2. `fermat_little`: since `p ∤ a`, `a ≠ 0` in `ZMod p`. From `a ^ (p - 1) * a = a ^ p = 1 * a`
   we cancel `a` and get `a ^ (p - 1) = 1` in `ZMod p`, i.e. `a ^ (p - 1) ≡ 1 [MOD p]`.
-/

namespace Prova04

/-- In `ZMod p`, with `p` prime, every natural number `a` satisfies `a ^ p = a`. -/
theorem natCast_pow_prime_eq_self {p : ℕ} [Fact p.Prime] (a : ℕ) :
    ((a : ZMod p)) ^ p = a := by
  induction a with
  | zero =>
    -- `0 ^ p = 0` because `p ≠ 0`.
    simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | succ k ih =>
    -- `(k + 1) ^ p = k ^ p + 1 ^ p = k + 1`.
    push_cast
    rw [add_pow_char, ih, one_pow]

/-- **Fermat's little theorem**: if `p` is prime and `p ∤ a`, then `a ^ (p - 1) ≡ 1 [MOD p]`. -/
theorem fermat_little {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) : a ^ (p - 1) ≡ 1 [MOD p] := by
  -- Make the primality of `p` available as an instance (needed by `add_pow_char`).
  have := Fact.mk hp
  -- `a` is nonzero modulo `p`.
  have hx : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact ha
  -- `a ^ (p - 1) * a = a ^ p = a = 1 * a`.
  have hpow : (a : ZMod p) ^ (p - 1) * a = 1 * a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul]
    exact natCast_pow_prime_eq_self a
  -- Cancel `a`, which is allowed because `ZMod p` is a field and `a ≠ 0`.
  have h1 : (a : ZMod p) ^ (p - 1) = 1 := mul_right_cancel₀ hx hpow
  -- Translate the equality in `ZMod p` back to a congruence of natural numbers.
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h1

/-- The same statement, obtained directly from the Mathlib version
`Nat.ModEq.pow_card_sub_one_eq_one`, which uses `Nat.Coprime a p` instead of `¬ p ∣ a`. -/
theorem fermat_little_mathlib {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] :=
  Nat.ModEq.pow_card_sub_one_eq_one hp ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha).symm

/-! ## Examples -/

-- `3 ^ 6 = 729 = 104 * 7 + 1`.
example : 3 ^ (7 - 1) ≡ 1 [MOD 7] := fermat_little Nat.prime_seven (by norm_num)

-- The hypotheses cannot be dropped (see the module docstring).
-- `p = 4` is not prime: `3 ^ 3 = 27 ≡ 3 [MOD 4]`.
example : ¬ 3 ^ (4 - 1) ≡ 1 [MOD 4] := by decide

-- `p = 3` divides `a = 6`: `6 ^ 2 = 36 ≡ 0 [MOD 3]`.
example : ¬ 6 ^ (3 - 1) ≡ 1 [MOD 3] := by decide

end Prova04
