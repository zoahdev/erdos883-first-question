import Erdos883CoprimeDiscrepancy
import Mathlib.RingTheory.Radical.NatInt

namespace Erdos883Verified

open UniqueFactorizationMonoid

/-- Removing repeated prime factors does not change coprimality with a positive modulus. -/
theorem coprime_radical_iff (w : ℕ) {D : ℕ} (hD : 0 < D) :
    Nat.Coprime w (radical D) ↔ Nat.Coprime w D := by
  constructor
  · intro h
    exact (h.pow_right D).of_dvd_right (Nat.dvd_radical_pow_self hD.ne')
  · intro h
    exact h.of_dvd_right radical_dvd_self

/-- The positive-prefix coprime count depends only on the prime support. -/
theorem coprimePrefixCount_radical (X : ℕ) {D : ℕ} (hD : 0 < D) :
    coprimePrefixCount X (radical D) = coprimePrefixCount X D := by
  simp only [coprimePrefixCount, coprime_radical_iff _ hD]

/-- The totient density also depends only on the prime support. -/
theorem totientDensity_radical {D : ℕ} (hD : 0 < D) :
    totientDensity (radical D) = totientDensity D := by
  rw [totientDensity_eq_prod (Nat.radical_pos D), totientDensity_eq_prod hD,
    Nat.primeFactors_radical]

/-- Sharp one-sided error as a function of the number of distinct prime factors.
Natural subtraction gives zero at both zero and one prime factor. -/
def coprimeDiscrepancyError (w : ℕ) : ℕ := 2 ^ (w - 1) - 1

@[simp] theorem coprimeDiscrepancyError_zero : coprimeDiscrepancyError 0 = 0 := by
  rfl

@[simp] theorem coprimeDiscrepancyError_one : coprimeDiscrepancyError 1 = 0 := by
  rfl

/-- Enlarging a prime-support budget only enlarges the permitted error. -/
theorem coprimeDiscrepancyError_mono : Monotone coprimeDiscrepancyError := by
  intro w W h
  exact Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right h 1)) 1

/-- The squarefree discrepancy bound extends to every positive modulus via its radical. -/
theorem coprimePrefixCount_ge_density_sub_error_of_pos (X : ℕ) {D : ℕ}
    (hD : 0 < D) :
    (X : ℚ) * totientDensity D -
      (coprimeDiscrepancyError D.primeFactors.card : ℚ) ≤ coprimePrefixCount X D := by
  by_cases hD1 : D = 1
  · subst D
    simp [coprimePrefixCount_one, totientDensity, coprimeDiscrepancyError]
  · have hrad : 1 < radical D := Nat.one_lt_radical_iff.mpr (by omega)
    have h := coprimePrefixCount_ge_density_sub_error X squarefree_radical hrad
    simpa only [coprimePrefixCount_radical X hD, totientDensity_radical hD,
      Nat.primeFactors_radical, coprimeDiscrepancyError] using h

/-- A bound on the number of distinct prime factors yields a uniform discrepancy budget. -/
theorem coprimePrefixCount_ge_density_sub_error_of_card_le (X : ℕ) {D W : ℕ}
    (hD : 0 < D) (hW : D.primeFactors.card ≤ W) :
    (X : ℚ) * totientDensity D -
      (coprimeDiscrepancyError W : ℚ) ≤ coprimePrefixCount X D := by
  have he : (coprimeDiscrepancyError D.primeFactors.card : ℚ) ≤
      (coprimeDiscrepancyError W : ℚ) :=
    Nat.cast_le.mpr (coprimeDiscrepancyError_mono hW)
  exact (sub_le_sub_left he _).trans
    (coprimePrefixCount_ge_density_sub_error_of_pos X hD)

/-- Sharp density lower bound for the full raw common-coprime neighbor pool. -/
theorem rawCommon_coprime_Icc_card_ge_density_sub_error (L : ℕ) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    (L : ℚ) * totientDensity (Nat.lcm u v) -
      (coprimeDiscrepancyError (Nat.lcm u v).primeFactors.card : ℚ) ≤
        (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card := by
  rw [rawCommon_coprime_Icc_card]
  exact coprimePrefixCount_ge_density_sub_error_of_pos L (Nat.lcm_pos hu hv)

/-- Sharp density lower bound for the even raw common-coprime neighbor pool. -/
theorem rawCommon_coprime_even_card_ge_density_sub_error (L : ℕ) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v) :
    ((L / 2 : ℕ) : ℚ) * totientDensity (Nat.lcm u v) -
      (coprimeDiscrepancyError (Nat.lcm u v).primeFactors.card : ℚ) ≤
        (rawCommon Nat.Coprime (evenUniverse L) u v).card := by
  rw [rawCommon_coprime_even_card L huodd hvodd]
  exact coprimePrefixCount_ge_density_sub_error_of_pos (L / 2) (Nat.lcm_pos hu hv)

/-- Full-pool bound with any upper bound on the size of the joint prime support. -/
theorem rawCommon_coprime_Icc_card_ge_density_sub_error_of_card_le
    (L : ℕ) {u v W : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hW : (Nat.lcm u v).primeFactors.card ≤ W) :
    (L : ℚ) * totientDensity (Nat.lcm u v) -
      (coprimeDiscrepancyError W : ℚ) ≤
        (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card := by
  rw [rawCommon_coprime_Icc_card]
  exact coprimePrefixCount_ge_density_sub_error_of_card_le L (Nat.lcm_pos hu hv) hW

/-- Even-pool bound with any upper bound on the size of the joint prime support. -/
theorem rawCommon_coprime_even_card_ge_density_sub_error_of_card_le
    (L : ℕ) {u v W : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v)
    (hW : (Nat.lcm u v).primeFactors.card ≤ W) :
    ((L / 2 : ℕ) : ℚ) * totientDensity (Nat.lcm u v) -
      (coprimeDiscrepancyError W : ℚ) ≤
        (rawCommon Nat.Coprime (evenUniverse L) u v).card := by
  rw [rawCommon_coprime_even_card L huodd hvodd]
  exact coprimePrefixCount_ge_density_sub_error_of_card_le
    (L / 2) (Nat.lcm_pos hu hv) hW

#print axioms coprime_radical_iff
#print axioms coprimePrefixCount_radical
#print axioms totientDensity_radical
#print axioms coprimeDiscrepancyError_zero
#print axioms coprimeDiscrepancyError_one
#print axioms coprimeDiscrepancyError_mono
#print axioms coprimePrefixCount_ge_density_sub_error_of_pos
#print axioms coprimePrefixCount_ge_density_sub_error_of_card_le
#print axioms rawCommon_coprime_Icc_card_ge_density_sub_error
#print axioms rawCommon_coprime_even_card_ge_density_sub_error
#print axioms rawCommon_coprime_Icc_card_ge_density_sub_error_of_card_le
#print axioms rawCommon_coprime_even_card_ge_density_sub_error_of_card_le

end Erdos883Verified
