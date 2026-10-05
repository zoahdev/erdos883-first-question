import Erdos883ProfileCriterion
import Erdos883TailDensity
import Erdos883NeighborDiscrepancy
import Mathlib.Data.Rat.Floor

namespace Erdos883Verified

/-- For odd endpoints the prime 2 need not be present in the signature list. -/
theorem missingOddPrime_ge_of_signature_eq {u v p : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hvodd : Odd v)
    (hcover : ∀ q, q.Prime → q ≠ 2 → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v) :
    ∀ q ∈ v.primeFactors \ u.primeFactors, p ≤ q := by
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqv, hqu⟩
  have hq2 : q ≠ 2 := by
    intro he
    subst q
    have hd := Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hqv)
    have ho := Nat.odd_iff.mp hvodd
    omega
  by_contra hqp
  have hmem := hcover q (Nat.prime_of_mem_primeFactors hqv) hq2 (by omega)
  have hqu' : q ∣ u :=
    (divisorSignatureCode_eq_imp_dvd_iff ps u v hcode hmem).mpr
      (Nat.dvd_of_mem_primeFactors hqv)
  exact hqu ((Nat.mem_primeFactors_of_ne_zero hu.ne').mpr
    ⟨Nat.prime_of_mem_primeFactors hqv, hqu'⟩)

def adaptiveTailFactor (U p : ℕ) : ℚ :=
  (((p : ℚ) - 1) / p) ^ Nat.log p U

def adaptiveDensityLower (U p : ℕ) (z : ℚ) : ℚ :=
  max (z ^ 2) (z * adaptiveTailFactor U p)

/-- Product density and equal-signature tail density may be combined by maximum. -/
theorem adaptiveDensityLower_le_lcm {u v U p : ℕ} {ps : List ℕ} {z : ℚ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v) (hvU : v ≤ U) (hp : 2 ≤ p)
    (hcover : ∀ q, q.Prime → q ≠ 2 → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    (hz : 0 ≤ z) (hzu : z ≤ totientDensity u) (hzv : z ≤ totientDensity v) :
    adaptiveDensityLower U p z ≤ totientDensity (Nat.lcm u v) := by
  apply max_le
  · exact totientDensity_lcm_ge_sq hu hv hz hzu hzv
  · have hsmall := missingOddPrime_ge_of_signature_eq hu hvodd hcover hcode
    have htail := totientDensity_lcm_ge_tailFactor hu hv hp hsmall
      (primeFactors_subset_card_le_log hv hvU hp Finset.sdiff_subset hsmall)
    have heta : 0 ≤ adaptiveTailFactor U p :=
      pow_nonneg (thresholdFactor_mem_unitInterval hp).1 _
    exact (mul_le_mul_of_nonneg_right hzu heta).trans htail

/-- Natural floor clamps negative lower estimates to zero, which remains a valid
neighbor-cardinality lower bound. -/
def adaptiveDegree (scale U W p : ℕ) (z : ℚ) : ℕ :=
  ⌊(scale : ℚ) * adaptiveDensityLower U p z - coprimeDiscrepancyError W⌋₊

/-- The exact adaptive univariate degree functions have their promised raw-pool
meaning, provided a prime-support budget and small-prime coverage are supplied. -/
theorem adaptive_profile_degree_bounds (L U W : ℕ) (ps : List ℕ) (next : ℕ → ℕ)
    (hnext : ∀ s ≤ ps.length, 2 ≤ next s)
    (hcover : ∀ s ≤ ps.length, ∀ q, q.Prime → q ≠ 2 → q < next s → q ∈ ps.take s)
    (hW : ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U,
      (Nat.lcm u v).primeFactors.card ≤ W) :
    ProfileDegreeBounds totientDensity (fun z : ℚ => 0 ≤ z ∧ z ≤ 1) L U ps
      (fun s z => adaptiveDegree (L / 2) U W (next s) z)
      (fun s z => adaptiveDegree L U W (next s) z) := by
  intro s hs z hz u huU v hvU _hne hcode hzu hzv
  rcases Finset.mem_filter.mp huU with ⟨huI, huodd⟩
  rcases Finset.mem_filter.mp hvU with ⟨hvI, hvodd⟩
  rcases Finset.mem_Icc.mp huI with ⟨hu, huU'⟩
  rcases Finset.mem_Icc.mp hvI with ⟨hv, hvU'⟩
  have hlow := adaptiveDensityLower_le_lcm hu hv hvodd hvU' (hnext s hs)
    (hcover s hs) hcode hz.1 hzu hzv
  have hw := hW u (Finset.mem_filter.mpr ⟨huI, huodd⟩)
    v (Finset.mem_filter.mpr ⟨hvI, hvodd⟩)
  constructor
  · apply Nat.floor_le_of_le
    have hc := rawCommon_coprime_even_card_ge_density_sub_error_of_card_le L hu hv huodd hvodd hw
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg (L / 2))) _).trans hc
  · apply Nat.floor_le_of_le
    have hc := rawCommon_coprime_Icc_card_ge_density_sub_error_of_card_le L hu hv hw
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg L)) _).trans hc

#print axioms missingOddPrime_ge_of_signature_eq
#print axioms adaptiveDensityLower_le_lcm
#print axioms adaptive_profile_degree_bounds
end Erdos883Verified
