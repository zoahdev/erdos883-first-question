import Erdos883RefinedCdfReal
import Erdos883CdfEnvelope
import Mathlib.Analysis.Complex.Exponential

namespace Erdos883Verified
open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact Taylor arithmetic gives a convenient bound at the new endpoint. -/
theorem refined_log_20000_lt : Real.log 20000 < (991 : ℝ) / 100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 20000)).mpr
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 991 / 100) 21
  have hguard : (20000 : ℝ) <
      ∑ i ∈ Finset.range 21, ((991 : ℝ) / 100) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hguard.trans_le hsum

private theorem refined_log_div_self_antitone {x y : ℝ}
    (hx : 0 < x) (hlog : 1 ≤ Real.log x) (hxy : x ≤ y) :
    Real.log y / y ≤ Real.log x / x := by
  have hy : 0 < y := hx.trans_le hxy
  have hdiv : 0 ≤ y / x - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hx, zero_add, one_mul]
    exact hxy
  rw [div_le_iff₀ hy, ← sub_le_sub_iff_right (Real.log x)]
  calc
    Real.log y - Real.log x = Real.log (y / x) := by
      rw [Real.log_div hy.ne' hx.ne']
    _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
    _ ≤ Real.log x * (y / x - 1) := le_mul_of_one_le_left hdiv hlog
    _ = Real.log x / x * y - Real.log x := by ring

theorem refined_log_prefix_upper {n : ℕ} (hn : 200000 ≤ n) :
    Real.log ((n : ℝ) / 10) / n ≤ ((991 : ℝ) / 100) / 200000 := by
  have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 1 ≤ Real.log (20000 : ℝ) := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 19999)
    norm_num at h
    linarith
  have hx : (20000 : ℝ) ≤ (n : ℝ) / 10 := by linarith
  have hmono := refined_log_div_self_antitone (by norm_num) he hx
  have hlog : Real.log ((n : ℝ) / 10) / ((n : ℝ) / 10) ≤ (991 / 100) / 20000 :=
    hmono.trans (div_le_div_of_nonneg_right refined_log_20000_lt.le (by norm_num))
  calc
    _ = (1 / 10 : ℝ) * (Real.log ((n : ℝ) / 10) / ((n : ℝ) / 10)) := by ring
    _ ≤ (1 / 10 : ℝ) * ((991 / 100) / 20000) := mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = _ := by norm_num

/-- The exact finite states corresponding to the core-only numerical list. -/
def refinedCdfTrueState (c : Fin 16) : Rat × Rat × Rat :=
  (fourPrimeSmallDensity c, fourPrimeQ c, fourPrimeError c)

theorem refinedCdfTrueState_list : List.ofFn refinedCdfTrueState = refinedCdfStates := by
  decide +kernel

/-- Each actual state is bounded directly by its fixed-200000 cap and moment. -/
theorem refinedCdfStateLowCount_le {n : ℕ} (hn : 200000 ≤ n)
    (c : Fin 16) {t : ℝ} (ht : 0 < t) :
    (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      refinedCdfStateReal (refinedCdfTrueState c) t := by
  have hn0 : 0 < n := by omega
  have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hq : (0 : ℝ) ≤ (fourPrimeQ c : ℝ) := by exact_mod_cast fourPrimeQ_nonneg c
  have he : (0 : ℝ) ≤ (fourPrimeError c : ℝ) := by exact_mod_cast fourPrimeError_nonneg c
  have hmass := cdfStateLowCount_normalized_le_mass hn0 c t
  have hcap : (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      (fourPrimeQ c : ℝ) + 2 * (fourPrimeError c : ℝ) / 200000 := by
    apply hmass.trans
    exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) (by norm_num) hnR)
  unfold refinedCdfStateReal refinedCdfTrueState
  dsimp only
  split_ifs with hat
  · exact hcap
  · apply le_min hcap
    have hta : t < (fourPrimeSmallDensity c : ℝ) := lt_of_not_ge hat
    have hnum : (fourPrimeQ c : ℝ) * ((47 : ℝ) / 2000) +
        (fourPrimeError c : ℝ) * Real.log ((n : ℝ) / 10) / n ≤
        (fourPrimeQ c : ℝ) * (47 / 2000) + (fourPrimeError c : ℝ) * (991 / 100) / 200000 := by
      have h := mul_le_mul_of_nonneg_left (refined_log_prefix_upper hn) he
      simpa only [mul_div_assoc] using add_le_add (le_refl ((fourPrimeQ c : ℝ) * (47 / 2000))) h
    have hnum0 : 0 ≤ (fourPrimeQ c : ℝ) * (47 / 2000) +
        (fourPrimeError c : ℝ) * (991 / 100) / 200000 := by positivity
    have hlog : 0 < Real.log ((fourPrimeSmallDensity c : ℝ) / t) :=
      Real.log_pos ((one_lt_div ht).mpr hta)
    have hrpos : 0 < 2 * ((fourPrimeSmallDensity c : ℝ) - t) /
        ((fourPrimeSmallDensity c : ℝ) + t) := by
      exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hta)) (by linarith)
    calc
      _ ≤ ((fourPrimeQ c : ℝ) * (47 / 2000) +
          (fourPrimeError c : ℝ) * Real.log ((n : ℝ) / 10) / n) /
          Real.log ((fourPrimeSmallDensity c : ℝ) / t) :=
        cdfStateLowCount_normalized_le_log_explicit (by omega) c ht hta
      _ ≤ ((fourPrimeQ c : ℝ) * (47 / 2000) + (fourPrimeError c : ℝ) * (991 / 100) / 200000) /
          Real.log ((fourPrimeSmallDensity c : ℝ) / t) := div_le_div_of_nonneg_right hnum hlog.le
      _ ≤ ((fourPrimeQ c : ℝ) * (47 / 2000) + (fourPrimeError c : ℝ) * (991 / 100) / 200000) /
          (2 * ((fourPrimeSmallDensity c : ℝ) - t) / ((fourPrimeSmallDensity c : ℝ) + t)) :=
        div_le_div_of_nonneg_left hnum0 hrpos (cdf_rational_le_log ht hta)
      _ = _ := by field_simp

/-- Summing the true state bounds gives the exact fixed-endpoint envelope. -/
theorem totientCdf_le_refined_envelope {n : ℕ} (hn : 200000 ≤ n)
    {t : ℝ} (ht : 0 < t) : totientCdf n t ≤ refinedCdfBoundReal t := by
  unfold refinedCdfBoundReal
  apply le_min
  · exact (odd_totient_cdf_lt_twenty_two_real_uniform (by omega : 0 < n) ht).le
  · calc
      _ = ∑ c : Fin 16, (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) := totientCdf_eq_sum_states n t
      _ ≤ ∑ c : Fin 16, refinedCdfStateReal (refinedCdfTrueState c) t :=
        Finset.sum_le_sum (fun c _ => refinedCdfStateLowCount_le hn c ht)
      _ = _ := by
        rw [← List.sum_eq_foldl, ← refinedCdfTrueState_list, List.map_ofFn, List.sum_ofFn]
        rfl

#print axioms refined_log_20000_lt
#print axioms refined_log_prefix_upper
#print axioms refinedCdfTrueState_list
#print axioms refinedCdfStateLowCount_le
#print axioms totientCdf_le_refined_envelope
end Erdos883Verified
