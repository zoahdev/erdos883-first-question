import Erdos883TotientDensity
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Independent uniform prime-support error estimates for the near-U route.
No second-question proof is imported. -/

namespace Erdos883Second.Near

/-- A deliberately coarse, explicit constant; no estimate on prime growth. -/
def supportConstant (r : ℕ) : ℕ := 2 ^ (2 ^ r)

/-- Split the prime support at `2^r`. Large prime factors pay for the
`2^r` term directly, and at most `2^r` small prime factors pay a constant.
This is an integer-power estimate, valid for every positive integer. -/
theorem prime_support_power_bound (q r : ℕ) (hq : 0 < q) :
    (2 ^ q.primeFactors.card) ^ r ≤ supportConstant r ^ r * q := by
  classical
  let P := q.primeFactors
  let S := P.filter (fun p => p < 2 ^ r)
  have hsmall : S.card ≤ 2 ^ r := by
    have hs : S ⊆ Finset.range (2 ^ r) := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hs
  have hfactor : ∀ p ∈ P,
      2 ^ r ≤ (if p < 2 ^ r then 2 ^ r else 1) * p := by
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    split_ifs with h
    · simpa using Nat.mul_le_mul_left (2 ^ r) hp1
    · simpa using (show 2 ^ r ≤ p by omega)
  have hprod : ∏ p ∈ P, p ≤ q :=
    Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hweight : (∏ p ∈ P, if p < 2 ^ r then 2 ^ r else 1) =
      (2 ^ r) ^ S.card := by
    rw [← Finset.prod_filter]
    simp [S]
  calc
    (2 ^ q.primeFactors.card) ^ r = (2 ^ r) ^ P.card := by
      dsimp [P]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ∏ p ∈ P, 2 ^ r := by simp
    _ ≤ ∏ p ∈ P, (if p < 2 ^ r then 2 ^ r else 1) * p :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hfactor
    _ = (2 ^ r) ^ S.card * ∏ p ∈ P, p := by
      rw [Finset.prod_mul_distrib, hweight]
    _ ≤ (2 ^ r) ^ (2 ^ r) * q := by
      apply Nat.mul_le_mul _ hprod
      exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hsmall
    _ = supportConstant r ^ r * q := by
      simp only [supportConstant, ← pow_mul]
      rw [Nat.mul_comm r]

/-- Products of at most `d` numbers bounded by `n` can use the same bound.
The exponent `r` can be chosen much larger than `d`. -/
theorem prime_support_power_bound_of_le {q n d r : ℕ}
    (hq : 0 < q) (hqn : q ≤ n ^ d) :
    (2 ^ q.primeFactors.card) ^ r ≤ supportConstant r ^ r * n ^ d :=
  (prime_support_power_bound q r hq).trans
    (Nat.mul_le_mul_left _ hqn)

#print axioms prime_support_power_bound
#print axioms prime_support_power_bound_of_le

end Erdos883Second.Near
