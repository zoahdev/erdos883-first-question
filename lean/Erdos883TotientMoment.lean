import Erdos883TotientDensity
import Erdos883ParityCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

namespace Erdos883Verified

/-- Distinct primes have product dividing `v` exactly when each prime divides `v`. -/
theorem prime_finset_prod_dvd_iff (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (v : ℕ) :
    (∏ p ∈ P, p) ∣ v ↔ ∀ p ∈ P, p ∣ v := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · intro h
    by_cases hv : v = 0
    · simp [hv]
    · have hs : P ⊆ v.primeFactors := by
        intro p hp
        exact (Nat.mem_primeFactors_of_ne_zero hv).mpr ⟨hP p hp, h p hp⟩
      exact (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans (Nat.prod_primeFactors_dvd v)

/-- Counting positive multiples in the interval used by the finite moment argument. -/
theorem card_Icc_filter_dvd (n d : ℕ) :
    ((Finset.Icc 1 n).filter (fun v => d ∣ v)).card = n / d := by
  have hi : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext v
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hi]
  exact Nat.Ioc_filter_dvd_card_eq_div n d

/-- An indicator-product expansion for one subset of the prime support. -/
theorem prod_dvd_indicator (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℚ) (v : ℕ) :
    (∏ p ∈ P, if p ∣ v then a p else 0) =
      if (∏ p ∈ P, p) ∣ v then ∏ p ∈ P, a p else 0 := by
  by_cases h : (∏ p ∈ P, p) ∣ v
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun p hp => if_pos ((prime_finset_prod_dvd_iff P hP v).mp h p hp)
  · rw [if_neg h]
    have hn : ¬ ∀ p ∈ P, p ∣ v := by
      simpa only [← prime_finset_prod_dvd_iff P hP v] using h
    push Not at hn
    obtain ⟨p, hp, hd⟩ := hn
    exact Finset.prod_eq_zero hp (if_neg hd)

/-- Exact finite expansion of a multiplicative prime weight over a positive interval. -/
theorem weighted_prime_sum_eq (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℚ) :
    (∑ v ∈ Finset.Icc 1 n, ∏ p ∈ P, (1 + if p ∣ v then a p else 0)) =
      ∑ T ∈ P.powerset, (n / (∏ p ∈ T, p) : ℕ) * ∏ p ∈ T, a p := by
  simp_rw [Finset.prod_one_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  have hTP : ∀ p ∈ T, p.Prime := fun p hp => hP p ((Finset.mem_powerset.mp hT) hp)
  simp_rw [prod_dvd_indicator T hTP]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, card_Icc_filter_dvd]

/-- Finite weighted-prime moment bound. No asymptotic equidistribution is needed. -/
theorem weighted_prime_sum_le (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℚ) (ha : ∀ p ∈ P, 0 ≤ a p) :
    (∑ v ∈ Finset.Icc 1 n, ∏ p ∈ P, (1 + if p ∣ v then a p else 0)) ≤
      (n : ℚ) * ∏ p ∈ P, (1 + a p / p) := by
  rw [weighted_prime_sum_eq n P hP a, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hnonneg : 0 ≤ ∏ p ∈ T, a p :=
    Finset.prod_nonneg fun p hp => ha p ((Finset.mem_powerset.mp hT) hp)
  calc
    ((n / (∏ p ∈ T, p) : ℕ) : ℚ) * (∏ p ∈ T, a p) ≤
        ((n : ℚ) / (∏ p ∈ T, p : ℕ)) * (∏ p ∈ T, a p) :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le hnonneg
    _ = (n : ℚ) * ∏ p ∈ T, (a p / p) := by
      rw [Finset.prod_div_distrib, Nat.cast_prod]
      ring

/-- The same moment bound in filtered-product notation. -/
theorem weighted_prime_filter_sum_le (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℚ) (ha : ∀ p ∈ P, 0 ≤ a p) :
    (∑ v ∈ Finset.Icc 1 n, ∏ p ∈ P.filter (fun p => p ∣ v), (1 + a p)) ≤
      (n : ℚ) * ∏ p ∈ P, (1 + a p / p) := by
  convert weighted_prime_sum_le n P hP a ha using 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  split_ifs <;> simp

/-- The nonnegative increment used for the sixth inverse-totient moment. -/
def totientMomentWeight (p : ℕ) : ℚ := ((p : ℚ) / ((p : ℚ) - 1)) ^ 6 - 1

/-- The finite Euler product controlling the sixth inverse-totient moment. -/
def totientEulerProduct (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P, (1 + totientMomentWeight p / p)

theorem totientMomentWeight_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ totientMomentWeight p := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hratio : (1 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hpq)).mpr
    linarith
  exact sub_nonneg.mpr (one_le_pow₀ hratio)

/-- Sixth inverse density as a product over the distinct prime factors. -/
theorem inv_totientDensity_pow_six_eq_prod {v : ℕ} (hv : 0 < v) :
    (totientDensity v)⁻¹ ^ 6 =
      ∏ p ∈ v.primeFactors, (1 + totientMomentWeight p) := by
  rw [totientDensity_eq_prod hv, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors_of_ne_zero hv.ne').mp hp
  have hpq : (1 : ℚ) < p := by exact_mod_cast hprime.1.one_lt
  have hp0 : (p : ℚ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hpq)
  have hp1 : (p : ℚ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpq)
  have hi : (1 - (p : ℚ)⁻¹)⁻¹ = (p : ℚ) / ((p : ℚ) - 1) := by
    field_simp
  rw [hi]
  simp [totientMomentWeight]

/-- If `P` contains all prime divisors of `v`, its divisor filter is exact. -/
theorem prime_filter_eq_primeFactors {v : ℕ} (hv : 0 < v) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hs : v.primeFactors ⊆ P) :
    P.filter (fun p => p ∣ v) = v.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hv.ne']
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨hP p hp, hd⟩
  · intro h
    exact ⟨hs ((Nat.mem_primeFactors_of_ne_zero hv.ne').mpr h), h.2⟩

/-- An odd-interval sixth moment bound, with arbitrary finite containing prime support. -/
theorem odd_totient_sixth_moment_le (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ v ∈ oddUniverse n, v.primeFactors ⊆ P) :
    (∑ v ∈ oddUniverse n, (totientDensity v)⁻¹ ^ 6) ≤
      (n : ℚ) * totientEulerProduct P := by
  calc
    (∑ v ∈ oddUniverse n, (totientDensity v)⁻¹ ^ 6) =
        ∑ v ∈ oddUniverse n, ∏ p ∈ P.filter (fun p => p ∣ v),
          (1 + totientMomentWeight p) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
      rw [prime_filter_eq_primeFactors hvpos P hP (hs v hv),
        inv_totientDensity_pow_six_eq_prod hvpos]
    _ ≤ ∑ v ∈ Finset.Icc 1 n, ∏ p ∈ P.filter (fun p => p ∣ v),
          (1 + totientMomentWeight p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v hv hvo
      apply Finset.prod_nonneg
      intro p hp
      exact add_nonneg (by norm_num)
        (totientMomentWeight_nonneg (hP p (Finset.mem_filter.mp hp).1))
    _ ≤ (n : ℚ) * totientEulerProduct P :=
      weighted_prime_filter_sum_le n P hP totientMomentWeight
        (fun p hp => totientMomentWeight_nonneg (hP p hp))

/-- All prime divisors appearing among the positive odd integers at most `n`. -/
def oddPrimeSupport (n : ℕ) : Finset ℕ :=
  (oddUniverse n).biUnion Nat.primeFactors

theorem oddPrimeSupport_prime {n p : ℕ} (hp : p ∈ oddPrimeSupport n) : p.Prime := by
  obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hpv

theorem primeFactors_subset_oddPrimeSupport {n v : ℕ} (hv : v ∈ oddUniverse n) :
    v.primeFactors ⊆ oddPrimeSupport n := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨v, hv, hp⟩

/-- The canonical finite sixth moment estimate, with no prime-support hypotheses. -/
theorem odd_totient_sixth_moment_le_canonical (n : ℕ) :
    (∑ v ∈ oddUniverse n, (totientDensity v)⁻¹ ^ 6) ≤
      (n : ℚ) * totientEulerProduct (oddPrimeSupport n) :=
  odd_totient_sixth_moment_le n (oddPrimeSupport n)
    (fun _ hp => oddPrimeSupport_prime hp)
    (fun _ hv => primeFactors_subset_oddPrimeSupport hv)

theorem oddPrimeSupport_ne_two {n p : ℕ} (hp : p ∈ oddPrimeSupport n) : p ≠ 2 := by
  obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.mp hp
  have hvodd := (Finset.mem_filter.mp hv).2
  intro heq
  subst p
  exact hvodd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hpv)

theorem oddPrimeSupport_three_le {n p : ℕ} (hp : p ∈ oddPrimeSupport n) : 3 ≤ p := by
  have hp2 := (oddPrimeSupport_prime hp).two_le
  have hne := oddPrimeSupport_ne_two hp
  omega

theorem oddPrimeSupport_le {n p : ℕ} (hp : p ∈ oddPrimeSupport n) : p ≤ n := by
  obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hvpos, hvn⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
  exact (Nat.le_of_dvd hvpos (Nat.dvd_of_mem_primeFactors hpv)).trans hvn

/-- Finite Markov inequality for the small-totient subset. -/
theorem odd_totient_below_card_le_moment (n : ℕ) {t : ℚ} (ht : 0 < t) :
    (((oddUniverse n).filter (fun v => totientDensity v < t)).card : ℚ) ≤
      t ^ 6 * ∑ v ∈ oddUniverse n, (totientDensity v)⁻¹ ^ 6 := by
  rw [Finset.mul_sum]
  calc
    (((oddUniverse n).filter (fun v => totientDensity v < t)).card : ℚ) =
        ∑ v ∈ (oddUniverse n).filter (fun v => totientDensity v < t), (1 : ℚ) := by simp
    _ ≤ ∑ v ∈ (oddUniverse n).filter (fun v => totientDensity v < t),
        t ^ 6 * (totientDensity v)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvu, hvt⟩ := Finset.mem_filter.mp hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hvu).1).1
      have hrho := totientDensity_pos hvpos
      have hone : (1 : ℚ) ≤ t * (totientDensity v)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (one_le_div hrho).mpr hvt.le
      simpa only [mul_pow] using (one_le_pow₀ hone (n := 6))
    _ ≤ ∑ v ∈ oddUniverse n, t ^ 6 * (totientDensity v)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v hv hvo
      exact mul_nonneg (pow_nonneg ht.le 6)
        (pow_nonneg (inv_nonneg.mpr (totientDensity_nonneg v)) 6)

/-- The actual rational small-totient CDF is controlled by the finite Euler product. -/
theorem odd_totient_cdf_le_euler {n : ℕ} (hn : 0 < n) {t : ℚ} (ht : 0 < t) :
    (2 / (n : ℚ)) * (((oddUniverse n).filter
      (fun v => totientDensity v < t)).card : ℚ) ≤
      2 * totientEulerProduct (oddPrimeSupport n) * t ^ 6 := by
  have hcount := (odd_totient_below_card_le_moment n ht).trans
    (mul_le_mul_of_nonneg_left (odd_totient_sixth_moment_le_canonical n)
      (pow_nonneg ht.le 6))
  have hnq : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hscaled := mul_le_mul_of_nonneg_left hcount
    (div_nonneg (by norm_num : (0 : ℚ) ≤ 2) hnq.le)
  calc
    _ ≤ 2 / (n : ℚ) * (t ^ 6 * ((n : ℚ) *
        totientEulerProduct (oddPrimeSupport n))) := hscaled
    _ = _ := by field_simp [hnq.ne']

/-- The constant `11` remains an explicit analytic hypothesis, not an axiom. -/
theorem odd_totient_cdf_lt_twenty_two {n : ℕ} (hn : 0 < n)
    (hEuler : totientEulerProduct (oddPrimeSupport n) < 11)
    {t : ℚ} (ht : 0 < t) :
    (2 / (n : ℚ)) * (((oddUniverse n).filter
      (fun v => totientDensity v < t)).card : ℚ) < 22 * t ^ 6 := by
  apply (odd_totient_cdf_le_euler hn ht).trans_lt
  have ht6 : 0 < t ^ 6 := pow_pos ht 6
  nlinarith

/-- The same checked finite moment bound in the real field. -/
theorem odd_totient_sixth_moment_le_real (n : ℕ) :
    (∑ v ∈ oddUniverse n, ((totientDensity v : ℝ)⁻¹) ^ 6) ≤
      (n : ℝ) * (totientEulerProduct (oddPrimeSupport n) : ℝ) := by
  exact_mod_cast odd_totient_sixth_moment_le_canonical n

/-- Markov's inequality for arbitrary real thresholds, applied to the actual density. -/
theorem odd_totient_below_card_le_moment_real (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (((oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t)).card : ℝ) ≤
      t ^ 6 * ∑ v ∈ oddUniverse n, ((totientDensity v : ℝ)⁻¹) ^ 6 := by
  classical
  rw [Finset.mul_sum]
  calc
    (((oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t)).card : ℝ) =
        ∑ v ∈ (oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t), (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ (oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t),
        t ^ 6 * ((totientDensity v : ℝ)⁻¹) ^ 6 := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvu, hvt⟩ := Finset.mem_filter.mp hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hvu).1).1
      have hrho : (0 : ℝ) < totientDensity v := by exact_mod_cast totientDensity_pos hvpos
      have hone : (1 : ℝ) ≤ t * (totientDensity v : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (one_le_div hrho).mpr hvt.le
      simpa only [mul_pow] using (one_le_pow₀ hone (n := 6))
    _ ≤ ∑ v ∈ oddUniverse n, t ^ 6 * ((totientDensity v : ℝ)⁻¹) ^ 6 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v hv hvo
      have hrho : (0 : ℝ) ≤ totientDensity v := by exact_mod_cast totientDensity_nonneg v
      exact mul_nonneg (pow_nonneg ht.le 6) (pow_nonneg (inv_nonneg.mpr hrho) 6)

/-- Euler-product control of the actual finite CDF for every positive real threshold. -/
theorem odd_totient_cdf_le_euler_real {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (2 / (n : ℝ)) * (((oddUniverse n).filter
      (fun v => (totientDensity v : ℝ) < t)).card : ℝ) ≤
      2 * (totientEulerProduct (oddPrimeSupport n) : ℝ) * t ^ 6 := by
  classical
  have hcount := (odd_totient_below_card_le_moment_real n ht).trans
    (mul_le_mul_of_nonneg_left (odd_totient_sixth_moment_le_real n)
      (pow_nonneg ht.le 6))
  have hnq : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscaled := mul_le_mul_of_nonneg_left hcount
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnq.le)
  calc
    _ ≤ 2 / (n : ℝ) * (t ^ 6 * ((n : ℝ) *
        (totientEulerProduct (oddPrimeSupport n) : ℝ))) := hscaled
    _ = _ := by field_simp [hnq.ne']

/-- The real-threshold CDF estimate, conditional only on the explicit finite Euler bound. -/
theorem odd_totient_cdf_lt_twenty_two_real {n : ℕ} (hn : 0 < n)
    (hEuler : totientEulerProduct (oddPrimeSupport n) < 11)
    {t : ℝ} (ht : 0 < t) :
    (2 / (n : ℝ)) * (((oddUniverse n).filter
      (fun v => (totientDensity v : ℝ) < t)).card : ℝ) < 22 * t ^ 6 := by
  classical
  apply (odd_totient_cdf_le_euler_real hn ht).trans_lt
  have ht6 : 0 < t ^ 6 := pow_pos ht 6
  have hEulerR : (totientEulerProduct (oddPrimeSupport n) : ℝ) < 11 := by
    exact_mod_cast hEuler
  nlinarith

end Erdos883Verified

#print axioms Erdos883Verified.weighted_prime_sum_eq
#print axioms Erdos883Verified.weighted_prime_sum_le
#print axioms Erdos883Verified.weighted_prime_filter_sum_le

#print axioms Erdos883Verified.odd_totient_sixth_moment_le_canonical

#print axioms Erdos883Verified.odd_totient_cdf_lt_twenty_two

#print axioms Erdos883Verified.odd_totient_cdf_lt_twenty_two_real
