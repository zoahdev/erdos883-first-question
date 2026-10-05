import Erdos883TotientDensity
import Erdos883PrimeSignatures
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Erdos883Verified

/-- Only the prime divisors introduced by `v` contribute a new Euler factor. -/
theorem totientDensity_lcm_eq_mul_prod_sdiff {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    totientDensity (Nat.lcm u v) = totientDensity u *
      ∏ q ∈ v.primeFactors \ u.primeFactors, (1 - (q : ℚ)⁻¹) := by
  have hd : Disjoint u.primeFactors (v.primeFactors \ u.primeFactors) := by
    exact Finset.disjoint_left.mpr (fun q hq hq' => (Finset.mem_sdiff.mp hq').2 hq)
  rw [totientDensity_eq_prod (Nat.lcm_pos hu hv), totientDensity_eq_prod hu,
    primeFactors_lcm hu hv, ← Finset.prod_union hd,
    Finset.union_sdiff_self_eq_union]

/-- Euler factors increase with the positive prime threshold. -/
theorem eulerFactor_lower_bound {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    ((p : ℚ) - 1) / (p : ℚ) ≤ 1 - (q : ℚ)⁻¹ := by
  have hp0 : (0 : ℚ) < p := Nat.cast_pos.mpr (by omega)
  have hpq' : (p : ℚ) ≤ q := Nat.cast_le.mpr hpq
  have h := inv_anti₀ hp0 hpq'
  calc
    ((p : ℚ) - 1) / (p : ℚ) = 1 - (p : ℚ)⁻¹ := by
      rw [sub_div, div_self hp0.ne', one_div]
    _ ≤ 1 - (q : ℚ)⁻¹ := sub_le_sub_left h 1

/-- The threshold factor lies in the unit interval. -/
theorem thresholdFactor_mem_unitInterval {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ ((p : ℚ) - 1) / (p : ℚ) ∧
      ((p : ℚ) - 1) / (p : ℚ) ≤ 1 := by
  have hp0 : (0 : ℚ) < p := Nat.cast_pos.mpr (by omega)
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast (show (1 : ℕ) ≤ p by omega)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hp1) hp0.le
  · apply (div_le_one₀ hp0).mpr
    exact sub_le_self _ (by decide)

/-- A product of Euler factors is bounded below using its cardinality and
 a lower bound for all of its primes. -/
theorem thresholdFactor_pow_card_le_prod {s : Finset ℕ} {p : ℕ}
    (hp : 2 ≤ p) (hs : ∀ q ∈ s, p ≤ q) :
    (((p : ℚ) - 1) / (p : ℚ)) ^ s.card ≤
      ∏ q ∈ s, (1 - (q : ℚ)⁻¹) := by
  calc
    _ = ∏ _q ∈ s, (((p : ℚ) - 1) / (p : ℚ)) := by rw [Finset.prod_const]
    _ ≤ _ := Finset.prod_le_prod
      (fun _ _ => (thresholdFactor_mem_unitInterval hp).1)
      (fun q hq => eulerFactor_lower_bound hp (hs q hq))

/-- The adaptive tail-factor estimate. The count is only of new prime divisors. -/
theorem totientDensity_lcm_ge_tailFactor {u v p a : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hp : 2 ≤ p)
    (hsmall : ∀ q ∈ v.primeFactors \ u.primeFactors, p ≤ q)
    (hcard : (v.primeFactors \ u.primeFactors).card ≤ a) :
    totientDensity u * (((p : ℚ) - 1) / (p : ℚ)) ^ a ≤
      totientDensity (Nat.lcm u v) := by
  rw [totientDensity_lcm_eq_mul_prod_sdiff hu hv]
  apply mul_le_mul_of_nonneg_left _ (totientDensity_nonneg u)
  exact (pow_le_pow_of_le_one (thresholdFactor_mem_unitInterval hp).1
    (thresholdFactor_mem_unitInterval hp).2 hcard).trans
      (thresholdFactor_pow_card_le_prod hp hsmall)


/-- A product of any subset of the distinct prime divisors still divides the integer. -/
theorem prod_primeFactors_subset_dvd {v : ℕ} {s : Finset ℕ}
    (hs : s ⊆ v.primeFactors) : (∏ q ∈ s, q) ∣ v := by
  exact (Finset.prod_dvd_prod_of_subset s v.primeFactors (fun q => q) hs).trans
    (Nat.prod_primeFactors_dvd v)

/-- Distinct prime divisors all at least `p` have a logarithmic count bound. -/
theorem primeFactors_subset_card_le_log {v U p : ℕ} {s : Finset ℕ}
    (hv : 0 < v) (hvU : v ≤ U) (hp : 2 ≤ p)
    (hs : s ⊆ v.primeFactors) (hsmall : ∀ q ∈ s, p ≤ q) :
    s.card ≤ Nat.log p U := by
  apply Nat.le_log_of_pow_le (by omega)
  calc
    p ^ s.card = ∏ _q ∈ s, p := by rw [Finset.prod_const]
    _ ≤ ∏ q ∈ s, q := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hsmall
    _ ≤ v := Nat.le_of_dvd hv (prod_primeFactors_subset_dvd hs)
    _ ≤ U := hvU

/-- Agreement on every listed small prime forces each newly introduced prime
 to be at least the threshold. Only completeness below the threshold is needed. -/
theorem missingPrime_ge_of_signature_eq {u v p : ℕ} {ps : List ℕ}
    (hu : 0 < u)
    (hcover : ∀ q, q.Prime → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v) :
    ∀ q ∈ v.primeFactors \ u.primeFactors, p ≤ q := by
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqv, hqu⟩
  by_contra hqp
  have hmem : q ∈ ps := hcover q (Nat.prime_of_mem_primeFactors hqv) (by omega)
  have hqu' : q ∣ u := (divisorSignatureCode_eq_imp_dvd_iff ps u v hcode hmem).mpr
    (Nat.dvd_of_mem_primeFactors hqv)
  exact hqu ((Nat.mem_primeFactors_of_ne_zero hu.ne').mpr
    ⟨Nat.prime_of_mem_primeFactors hqv, hqu'⟩)

/-- The threshold and cardinality hypotheses may be supplied through equal
 small-prime signatures and an ambient upper bound on the second integer. -/
theorem totientDensity_lcm_ge_signature_tailFactor {u v U p : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvU : v ≤ U) (hp : 2 ≤ p)
    (hcover : ∀ q, q.Prime → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v) :
    totientDensity u * (((p : ℚ) - 1) / (p : ℚ)) ^ Nat.log p U ≤
      totientDensity (Nat.lcm u v) := by
  have hsmall := missingPrime_ge_of_signature_eq hu hcover hcode
  exact totientDensity_lcm_ge_tailFactor hu hv hp hsmall
    (primeFactors_subset_card_le_log hv hvU hp Finset.sdiff_subset hsmall)

/-- Equal binary-prefix quotients give the same adaptive estimate whenever
 that prefix contains every prime below the chosen threshold. -/
theorem totientDensity_lcm_ge_prefix_tailFactor {u v U p s : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvU : v ≤ U) (hp : 2 ≤ p)
    (hcover : ∀ q, q.Prime → q < p → q ∈ ps.take s)
    (hcode : divisorSignatureCode ps u / 2 ^ (ps.length - s) =
      divisorSignatureCode ps v / 2 ^ (ps.length - s)) :
    totientDensity u * (((p : ℚ) - 1) / (p : ℚ)) ^ Nat.log p U ≤
      totientDensity (Nat.lcm u v) := by
  apply totientDensity_lcm_ge_signature_tailFactor hu hv hvU hp hcover
  simpa only [divisorSignatureCode_take] using hcode

end Erdos883Verified

#print axioms Erdos883Verified.totientDensity_lcm_eq_mul_prod_sdiff
#print axioms Erdos883Verified.eulerFactor_lower_bound
#print axioms Erdos883Verified.thresholdFactor_mem_unitInterval
#print axioms Erdos883Verified.thresholdFactor_pow_card_le_prod
#print axioms Erdos883Verified.totientDensity_lcm_ge_tailFactor

#print axioms Erdos883Verified.prod_primeFactors_subset_dvd
#print axioms Erdos883Verified.primeFactors_subset_card_le_log
#print axioms Erdos883Verified.missingPrime_ge_of_signature_eq
#print axioms Erdos883Verified.totientDensity_lcm_ge_signature_tailFactor
#print axioms Erdos883Verified.totientDensity_lcm_ge_prefix_tailFactor
