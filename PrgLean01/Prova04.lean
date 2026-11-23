import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false

/-!
# Fermat's little theorem

If `p` is prime and `p` does not divide `a`, then `a ^ (p - 1) ≡ 1 (mod p)`.

The hypotheses are necessary: for `a = p = 2` we would get `2 ≡ 1 (mod 2)`, which is false.

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

end Prova04
