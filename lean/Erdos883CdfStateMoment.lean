import Erdos883LogTail
import Erdos883SignatureCounts
import Erdos883TotientDensity
import Erdos883TotientMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Prime

namespace Erdos883Verified
open Finset

set_option maxHeartbeats 800000

/-- Logarithmic loss of one Euler factor. -/
noncomputable def cdfPrimeWeight (p : ℕ) : ℝ :=
  Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- The actual logarithmic loss from prime factors exceeding eleven. -/
noncomputable def cdfTailLog (v : ℕ) : ℝ :=
  ∑ p ∈ v.primeFactors.filter (fun p => 11 < p), cdfPrimeWeight p

/-- All tail primes appearing in the finite odd universe. -/
def cdfTailPrimeSupport (n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter (fun p => 11 < p)

theorem cdfPrimeWeight_nonneg {p : ℕ} (hp : 1 < p) :
    0 ≤ cdfPrimeWeight p := by
  apply Real.log_nonneg
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
  linarith

theorem cdfTailLog_nonneg (v : ℕ) : 0 ≤ cdfTailLog v := by
  apply Finset.sum_nonneg
  intro p hp
  exact cdfPrimeWeight_nonneg (by have := (Finset.mem_filter.mp hp).2; omega)

/-- An odd prime at most eleven belongs to the four-prime head. -/
theorem cdf_small_prime_mem {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) (hle : p ≤ 11) :
    p ∈ fourPrimeSet := by
  have hp2 := hp.two_le
  have h : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [fourPrimeSet] at *

/-- For odd positive vertices the state support is exactly the small-prime support. -/
theorem fourPrimeSelected_code_eq_smallFactors {v : ℕ} (hv : 0 < v) (ho : Odd v) :
    fourPrimeSelected (fourPrimeCode v) = v.primeFactors.filter (fun p => p ≤ 11) := by
  rw [fourPrimeSelected_code]
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hv.ne']
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨⟨fourPrimeSet_prime p hp, hd⟩, ?_⟩
    simp only [fourPrimeSet, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  · rintro ⟨⟨hp, hd⟩, hle⟩
    refine ⟨cdf_small_prime_mem hp ?_ hle, hd⟩
    intro h
    subst p
    exact ho.not_two_dvd_nat hd

/-- Exact Euler-factor split into the four-prime head and the actual prime tail. -/
theorem totientDensity_eq_small_mul_tail {v : ℕ} (hv : 0 < v) (ho : Odd v) :
    totientDensity v = fourPrimeSmallDensity (fourPrimeCode v) *
      ∏ p ∈ v.primeFactors.filter (fun p => 11 < p), (1 - (p : ℚ)⁻¹) := by
  rw [totientDensity_eq_prod hv, fourPrimeSmallDensity_eq_prod,
    fourPrimeSelected_code_eq_smallFactors hv ho]
  simpa only [not_le] using
    (Finset.prod_filter_mul_prod_filter_not v.primeFactors (fun p => p ≤ 11)
      (fun p => (1 - (p : ℚ)⁻¹))).symm

theorem cdf_euler_factor_pos {p : ℕ} (hp : p.Prime) :
    (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  apply sub_pos.mpr
  exact (inv_lt_one₀ hp0).mpr hp'

/-- The exact logarithmic relation between the state head and totient density. -/
theorem cdfTailLog_eq_log_density_ratio {v : ℕ} (hv : 0 < v) (ho : Odd v) :
    Real.log ((fourPrimeSmallDensity (fourPrimeCode v) : ℝ) /
      (totientDensity v : ℝ)) = cdfTailLog v := by
  have ha : (0 : ℝ) < (fourPrimeSmallDensity (fourPrimeCode v) : ℝ) := by
    exact_mod_cast totientDensity_pos (fourPrimeA_pos (fourPrimeCode v))
  have hrho : (0 : ℝ) < (totientDensity v : ℝ) := by
    exact_mod_cast totientDensity_pos hv
  have heq : (totientDensity v : ℝ) =
      (fourPrimeSmallDensity (fourPrimeCode v) : ℝ) *
      ∏ p ∈ v.primeFactors.filter (fun p => 11 < p), (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (totientDensity_eq_small_mul_tail hv ho)
    push_cast at h
    exact h
  have hfac : ∀ p ∈ v.primeFactors.filter (fun p => 11 < p),
      (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    exact cdf_euler_factor_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  rw [Real.log_div ha.ne' hrho.ne', heq,
    Real.log_mul ha.ne' (Finset.prod_pos hfac).ne', Real.log_prod (fun p hp => (hfac p hp).ne')]
  simp only [sub_add_cancel_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : (1 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
  have hi : (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [← Real.log_inv, hi]
  rfl

/-- A low-density vertex has logarithmic loss exceeding its state threshold. -/
theorem cdfTailLog_gt_log_threshold {v : ℕ} (hv : 0 < v) (ho : Odd v)
    {t : ℝ} (ht : 0 < t) (hvt : (totientDensity v : ℝ) < t) :
    Real.log ((fourPrimeSmallDensity (fourPrimeCode v) : ℝ) / t) < cdfTailLog v := by
  rw [← cdfTailLog_eq_log_density_ratio hv ho]
  have ha : (0 : ℝ) < (fourPrimeSmallDensity (fourPrimeCode v) : ℝ) := by
    exact_mod_cast totientDensity_pos (fourPrimeA_pos (fourPrimeCode v))
  have hrho : (0 : ℝ) < (totientDensity v : ℝ) := by
    exact_mod_cast totientDensity_pos hv
  apply Real.log_lt_log (div_pos ha ht)
  exact div_lt_div_of_pos_left ha hrho hvt

/-- The tail on a vertex can be summed over the canonical finite support. -/
theorem cdfTailLog_eq_sum_support {n v : ℕ} (hv : v ∈ oddUniverse n) :
    cdfTailLog v = ∑ p ∈ cdfTailPrimeSupport n,
      if p ∣ v then cdfPrimeWeight p else 0 := by
  rw [← Finset.sum_filter]
  unfold cdfTailLog
  congr 1
  ext p
  have hvpos : 0 < v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
  simp only [cdfTailPrimeSupport, Finset.mem_filter]
  constructor
  · rintro ⟨hpv, hlarge⟩
    exact ⟨⟨primeFactors_subset_oddPrimeSupport hv hpv, hlarge⟩,
      Nat.dvd_of_mem_primeFactors hpv⟩
  · rintro ⟨⟨hp, hlarge⟩, hd⟩
    exact ⟨(Nat.mem_primeFactors_of_ne_zero hvpos.ne').mpr
      ⟨oddPrimeSupport_prime hp, hd⟩, hlarge⟩

/-- Exact weighted double-counting inside one actual four-prime state fiber. -/
theorem cdfTailLog_state_sum_eq (n : ℕ) (c : Fin 16) :
    (∑ v ∈ (oddUniverse n).filter (fun v => fourPrimeCode v = c), cdfTailLog v) =
      ∑ p ∈ cdfTailPrimeSupport n, (fourPrimeMultipleCount n p c : ℝ) * cdfPrimeWeight p := by
  calc
    _ = ∑ v ∈ (oddUniverse n).filter (fun v => fourPrimeCode v = c),
        ∑ p ∈ cdfTailPrimeSupport n, if p ∣ v then cdfPrimeWeight p else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact cdfTailLog_eq_sum_support (Finset.mem_filter.mp hv).1
    _ = ∑ p ∈ cdfTailPrimeSupport n,
        ∑ v ∈ (oddUniverse n).filter (fun v => fourPrimeCode v = c),
          if p ∣ v then cdfPrimeWeight p else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, fourPrimeMultipleCount]

theorem fourPrimeQ_nonneg (c : Fin 16) : 0 ≤ fourPrimeQ c := by
  exact div_nonneg (totientDensity_nonneg _) (Nat.cast_nonneg _)

theorem fourPrimeError_nonneg (c : Fin 16) : 0 ≤ fourPrimeError c := by
  unfold fourPrimeError
  positivity

/-- Actual state-tail first moment, using only two explicit finite prime-sum bounds. -/
theorem cdfTailLog_state_sum_le (n : ℕ) (c : Fin 16) {D L : ℝ}
    (hD : (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p / p) ≤ D)
    (hL : (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p) ≤ L) :
    (∑ v ∈ (oddUniverse n).filter (fun v => fourPrimeCode v = c), cdfTailLog v) ≤
      (fourPrimeQ c : ℝ) * n / 2 * D + (fourPrimeError c : ℝ) * L := by
  rw [cdfTailLog_state_sum_eq]
  have hq : (0 : ℝ) ≤ (fourPrimeQ c : ℝ) := by exact_mod_cast fourPrimeQ_nonneg c
  have he : (0 : ℝ) ≤ (fourPrimeError c : ℝ) := by exact_mod_cast fourPrimeError_nonneg c
  calc
    _ ≤ ∑ p ∈ cdfTailPrimeSupport n,
        ((fourPrimeQ c : ℝ) * n / (2 * p) + (fourPrimeError c : ℝ)) * cdfPrimeWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp, hlarge⟩ := Finset.mem_filter.mp hp
      have herr := (abs_le.mp (fourPrimeMultipleCount_error n (oddPrimeSupport_prime hp) hlarge c)).2
      have hrat : (fourPrimeMultipleCount n p c : ℚ) ≤
          fourPrimeQ c * n / (2 * p) + fourPrimeError c := by linarith
      have hr : (fourPrimeMultipleCount n p c : ℝ) ≤
          (fourPrimeQ c : ℝ) * n / (2 * p) + (fourPrimeError c : ℝ) := by exact_mod_cast hrat
      exact mul_le_mul_of_nonneg_right hr (cdfPrimeWeight_nonneg (by omega))
    _ = (fourPrimeQ c : ℝ) * n / 2 *
        (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p / p) +
        (fourPrimeError c : ℝ) * (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p) := by
      calc
        _ = ∑ p ∈ cdfTailPrimeSupport n,
            ((fourPrimeQ c : ℝ) * n / 2 * (cdfPrimeWeight p / p) +
              (fourPrimeError c : ℝ) * cdfPrimeWeight p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hD (by positivity))
      (mul_le_mul_of_nonneg_left hL he)

/-- The actual low-totient count within one state, with a real threshold. -/
noncomputable def cdfStateLowCount (n : ℕ) (c : Fin 16) (t : ℝ) : ℕ := by
  classical
  exact ((oddUniverse n).filter
    (fun v => fourPrimeCode v = c ∧ (totientDensity v : ℝ) < t)).card

/-- The low-density subfiber is contained in its entire state. -/
theorem cdfStateLowCount_le_count (n : ℕ) (c : Fin 16) (t : ℝ) :
    cdfStateLowCount n c t ≤ fourPrimeCount n c := by
  classical
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, hc, _⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, hc⟩

/-- State mass cap, including the explicit finite-prefix discrepancy. -/
theorem cdfStateLowCount_normalized_le_mass {n : ℕ} (hn : 0 < n)
    (c : Fin 16) (t : ℝ) :
    (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      (fourPrimeQ c : ℝ) + 2 * (fourPrimeError c : ℝ) / n := by
  have hrat : (fourPrimeCount n c : ℚ) ≤ fourPrimeQ c * n / 2 + fourPrimeError c := by
    have h := (abs_le.mp (fourPrimeCount_error n c)).2
    linarith
  have hr : (fourPrimeCount n c : ℝ) ≤
      (fourPrimeQ c : ℝ) * n / 2 + (fourPrimeError c : ℝ) := by exact_mod_cast hrat
  have hlow : (cdfStateLowCount n c t : ℝ) ≤ (fourPrimeCount n c : ℝ) :=
    Nat.cast_le.mpr (cdfStateLowCount_le_count n c t)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (2 / (n : ℝ)) * ((fourPrimeQ c : ℝ) * n / 2 + (fourPrimeError c : ℝ)) :=
      mul_le_mul_of_nonneg_left (hlow.trans hr) (by positivity)
    _ = _ := by field_simp

/-- Finite first-moment Markov bound inside the actual state fiber. -/
theorem cdfStateLowCount_mul_log_le (n : ℕ) (c : Fin 16) {t : ℝ} (ht : 0 < t) :
    (cdfStateLowCount n c t : ℝ) * Real.log ((fourPrimeSmallDensity c : ℝ) / t) ≤
      ∑ v ∈ (oddUniverse n).filter (fun v => fourPrimeCode v = c), cdfTailLog v := by
  classical
  calc
    _ = ∑ _v ∈ (oddUniverse n).filter
        (fun v => fourPrimeCode v = c ∧ (totientDensity v : ℝ) < t),
        Real.log ((fourPrimeSmallDensity c : ℝ) / t) := by
      simp only [Finset.sum_const, nsmul_eq_mul, cdfStateLowCount]
    _ ≤ ∑ v ∈ (oddUniverse n).filter
        (fun v => fourPrimeCode v = c ∧ (totientDensity v : ℝ) < t), cdfTailLog v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvu, hc, hvt⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvint, ho⟩ := Finset.mem_filter.mp hvu
      have hvpos : 0 < v := (Finset.mem_Icc.mp hvint).1
      simpa only [hc] using (cdfTailLog_gt_log_threshold hvpos ho ht hvt).le
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨hvu, hc, _⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hvu, hc⟩
      · intro v hv hnot
        exact cdfTailLog_nonneg v

/-- The normalized low-density state count from finite tail-prime moment bounds. -/
theorem cdfStateLowCount_normalized_le_log {n : ℕ} (hn : 0 < n) (c : Fin 16)
    {t D L : ℝ} (ht : 0 < t) (hta : t < (fourPrimeSmallDensity c : ℝ))
    (hD : (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p / p) ≤ D)
    (hL : (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p) ≤ L) :
    (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      ((fourPrimeQ c : ℝ) * D + 2 * (fourPrimeError c : ℝ) * L / n) /
        Real.log ((fourPrimeSmallDensity c : ℝ) / t) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log ((fourPrimeSmallDensity c : ℝ) / t) := by
    apply Real.log_pos
    exact (one_lt_div ht).mpr hta
  apply (le_div_iff₀ hlog).mpr
  calc
    _ = (2 / (n : ℝ)) * ((cdfStateLowCount n c t : ℝ) *
        Real.log ((fourPrimeSmallDensity c : ℝ) / t)) := by ring
    _ ≤ (2 / (n : ℝ)) * ((fourPrimeQ c : ℝ) * n / 2 * D + (fourPrimeError c : ℝ) * L) :=
      mul_le_mul_of_nonneg_left
        ((cdfStateLowCount_mul_log_le n c ht).trans (cdfTailLog_state_sum_le n c hD hL))
        (by positivity)
    _ = _ := by field_simp

/-- Canonical tail support has precisely the prime and size hypotheses needed by the logarithmic bounds. -/
theorem cdfTailPrimeSupport_spec {n p : ℕ} (hp : p ∈ cdfTailPrimeSupport n) :
    p.Prime ∧ 11 < p ∧ p ≤ n := by
  obtain ⟨hp, hlarge⟩ := Finset.mem_filter.mp hp
  exact ⟨oddPrimeSupport_prime hp, hlarge, oddPrimeSupport_le hp⟩

theorem cdfPrimeWeight_eq_logTailLambda (p : ℕ) : cdfPrimeWeight p = logTailLambda p := rfl

/-- The numerical first-moment constant applies to the actual finite tail support. -/
theorem cdfTailPrimeSupport_weighted_sum_le (n : ℕ) :
    (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p / p) ≤ (47 : ℝ) / 2000 := by
  simpa only [cdfPrimeWeight_eq_logTailLambda] using
    (logTailLambda_sum_lt (cdfTailPrimeSupport n)
      (fun p hp => ⟨(cdfTailPrimeSupport_spec hp).1, (cdfTailPrimeSupport_spec hp).2.1⟩)).le

/-- The unweighted loss is logarithmic in the actual finite-prefix endpoint. -/
theorem cdfTailPrimeSupport_sum_le_log {n : ℕ} (hn : 13 ≤ n) :
    (∑ p ∈ cdfTailPrimeSupport n, cdfPrimeWeight p) ≤
      (1 / 2 : ℝ) * Real.log ((n : ℝ) / 10) := by
  simpa only [cdfPrimeWeight_eq_logTailLambda] using
    logTailLambda_sum_le_log (cdfTailPrimeSupport n) hn
      (fun _ hp => cdfTailPrimeSupport_spec hp)

/-- A fully numerical finite-prefix logarithmic bound for each actual state count. -/
theorem cdfStateLowCount_normalized_le_log_explicit {n : ℕ} (hn : 13 ≤ n)
    (c : Fin 16) {t : ℝ} (ht : 0 < t) (hta : t < (fourPrimeSmallDensity c : ℝ)) :
    (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      ((fourPrimeQ c : ℝ) * ((47 : ℝ) / 2000) +
        (fourPrimeError c : ℝ) * Real.log ((n : ℝ) / 10) / n) /
        Real.log ((fourPrimeSmallDensity c : ℝ) / t) := by
  convert cdfStateLowCount_normalized_le_log (by omega : 0 < n) c ht hta
    (cdfTailPrimeSupport_weighted_sum_le n) (cdfTailPrimeSupport_sum_le_log hn) using 1 <;> ring

/-- The true low-density count is the sum of its sixteen actual state counts. -/
theorem cdfStateLowCount_partition (n : ℕ) (t : ℝ) :
    (∑ c : Fin 16, cdfStateLowCount n c t) =
      ((oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t)).card := by
  classical
  exact fourPrime_filter_card_partition n (fun v => (totientDensity v : ℝ) < t)

#print axioms cdfStateLowCount_normalized_le_log_explicit
#print axioms cdfStateLowCount_partition
#print axioms cdfTailLog_eq_log_density_ratio
#print axioms cdfTailLog_gt_log_threshold
#print axioms cdfTailLog_state_sum_eq
#print axioms cdfTailLog_state_sum_le
#print axioms cdfStateLowCount_normalized_le_mass
#print axioms cdfStateLowCount_normalized_le_log

end Erdos883Verified
