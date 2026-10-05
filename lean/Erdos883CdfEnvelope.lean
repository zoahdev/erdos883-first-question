import Erdos883CdfStateMoment
import Erdos883CdfInterpolation
import Erdos883EulerBound

namespace Erdos883Verified
open Finset

set_option maxHeartbeats 800000

/-- The normalized, actual finite odd-totient distribution. -/
noncomputable def totientCdf (n : ℕ) (t : ℝ) : ℝ := by
  classical
  exact (2 / (n : ℝ)) *
    (((oddUniverse n).filter (fun v => (totientDensity v : ℝ) < t)).card : ℝ)

/-- A rational lower bound for the logarithmic state threshold. -/
theorem cdf_rational_le_log {a t : ℝ} (ht : 0 < t) (hta : t < a) :
    2 * (a - t) / (a + t) ≤ Real.log (a / t) := by
  have hx : 0 ≤ a / t - 1 := by
    have : 1 < a / t := (one_lt_div ht).mpr hta
    linarith
  have h := Real.le_log_one_add_of_nonneg hx
  have harg : 1 + (a / t - 1) = a / t := by ring
  rw [harg] at h
  convert h using 1
  field_simp
  <;> ring

/-- The finite-prefix logarithm is large enough to absorb state-count errors. -/
theorem cdf_log_prefix_lower {n : ℕ} (hn : 13 ≤ n) :
    (47 : ℝ) / 1000 ≤ Real.log ((n : ℝ) / 10) := by
  have hnR : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have h := cdf_rational_le_log (a := (n : ℝ)) (t := 10) (by norm_num) (by linarith)
  have hb : (47 : ℝ) / 1000 ≤ 2 * ((n : ℝ) - 10) / ((n : ℝ) + 10) := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < n + 10)).mpr
    nlinarith
  exact hb.trans h

/-- Combining the exact mass cap and logarithmic moment incurs a uniform state error. -/
private theorem cdf_cap_log_combine {m q e n L a t D : ℝ}
    (hq : 0 ≤ q) (he : 0 ≤ e) (hn : 0 < n) (hD : 0 < D)
    (hL : 2 * D ≤ L) (ht : 0 < t) (hta : t < a)
    (hmass : m ≤ q + 2 * e / n)
    (hmoment : m ≤ (q * D + e * L / n) / Real.log (a / t)) :
    m ≤ q * min 1 (D * (a + t) / (2 * (a - t))) + (e * L / n) / D := by
  let r : ℝ := 2 * (a - t) / (a + t)
  have ha : 0 < a := ht.trans hta
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hrl : r ≤ Real.log (a / t) := cdf_rational_le_log ht hta
  have hlog : 0 < Real.log (a / t) := hr.trans_le hrl
  have hL0 : 0 ≤ L := by linarith
  have hb : 0 ≤ e * L / n := by positivity
  have hidentity : D * (a + t) / (2 * (a - t)) = D / r := by
    dsimp [r]
    field_simp
  rw [hidentity]
  by_cases hrD : r ≤ D
  · have hmin : min 1 (D / r) = 1 := min_eq_left ((le_div_iff₀ hr).mpr (by simpa using hrD))
    rw [hmin, mul_one]
    apply hmass.trans
    apply add_le_add le_rfl
    apply (le_div_iff₀ hD).mpr
    calc
      2 * e / n * D = (e / n) * (2 * D) := by ring
      _ ≤ (e / n) * L := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = e * L / n := by ring
  · have hDr : D ≤ r := le_of_lt (lt_of_not_ge hrD)
    have hmin : min 1 (D / r) = D / r := min_eq_right ((div_le_one hr).mpr hDr)
    rw [hmin]
    calc
      m ≤ (q * D + e * L / n) / Real.log (a / t) := hmoment
      _ ≤ (q * D + e * L / n) / r :=
        div_le_div_of_nonneg_left (by positivity) hr hrl
      _ = q * (D / r) + (e * L / n) / r := by ring
      _ ≤ q * (D / r) + (e * L / n) / D :=
        add_le_add le_rfl (div_le_div_of_nonneg_left hb hD hDr)

/-- Every actual state is controlled by its matching certificate summand. -/
theorem cdfStateLowCount_le_state_add_error {n : ℕ} (hn : 13 ≤ n)
    (c : Fin 16) {t : ℝ} (ht : 0 < t) :
    (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) ≤
      cdfStateReal (fourPrimeState c) t +
        (2000 / 47 : ℝ) * (fourPrimeError c : ℝ) * Real.log ((n : ℝ) / 10) / n := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hq : (0 : ℝ) ≤ (fourPrimeQ c : ℝ) := by exact_mod_cast fourPrimeQ_nonneg c
  have he : (0 : ℝ) ≤ (fourPrimeError c : ℝ) := by exact_mod_cast fourPrimeError_nonneg c
  have hL := cdf_log_prefix_lower hn
  have hmass := cdfStateLowCount_normalized_le_mass hn0 c t
  unfold cdfStateReal
  rw [← fourPrimeSmallDensity_eq_state, ← fourPrimeQ_eq_state]
  split_ifs with hat
  · apply hmass.trans
    apply add_le_add le_rfl
    have hmul := mul_le_mul_of_nonneg_left hL
      (div_nonneg he (le_of_lt hnR))
    calc
      2 * (fourPrimeError c : ℝ) / n =
          (2000 / 47 : ℝ) * ((fourPrimeError c : ℝ) / n * (47 / 1000)) := by ring
      _ ≤ (2000 / 47 : ℝ) * ((fourPrimeError c : ℝ) / n * Real.log ((n : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by ring
  · have hta : t < (fourPrimeSmallDensity c : ℝ) := lt_of_not_ge hat
    have h := cdf_cap_log_combine hq he hnR (by norm_num : (0 : ℝ) < 47 / 2000)
      (by nlinarith : 2 * ((47 : ℝ) / 2000) ≤ Real.log ((n : ℝ) / 10))
      ht hta hmass (cdfStateLowCount_normalized_le_log_explicit hn c ht hta)
    convert h using 1 <;> ring

/-- The finite-state summation is exactly the list used in the checked certificates. -/
theorem cdfStateReal_sum_eq (t : ℝ) :
    (∑ c : Fin 16, cdfStateReal (fourPrimeState c) t) =
      ((states.map (fun aq => cdfStateReal aq t)).foldl (· + ·) 0) := by
  have hs : List.ofFn fourPrimeState = states := by decide +kernel
  rw [← List.sum_eq_foldl, ← hs, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Exact partition of the actual CDF into its sixteen state fibers. -/
theorem totientCdf_eq_sum_states (n : ℕ) (t : ℝ) :
    totientCdf n t = ∑ c : Fin 16, (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) := by
  classical
  unfold totientCdf
  rw [← cdfStateLowCount_partition]
  push_cast
  rw [Finset.mul_sum]

/-- Actual finite-prefix CDF domination by the sixteen-state certificate expression. -/
theorem totientCdf_le_state_sum_add_error {n : ℕ} (hn : 13 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    totientCdf n t ≤
      ((states.map (fun aq => cdfStateReal aq t)).foldl (· + ·) 0) +
        (81000 / 47 : ℝ) * Real.log ((n : ℝ) / 10) / n := by
  have heSum : (∑ c : Fin 16, (fourPrimeError c : ℝ)) = 81 / 2 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) fourPrimeError_sum
    push_cast at h
    exact h
  calc
    totientCdf n t = ∑ c : Fin 16,
        (2 / (n : ℝ)) * (cdfStateLowCount n c t : ℝ) := totientCdf_eq_sum_states n t
    _ ≤ ∑ c : Fin 16, (cdfStateReal (fourPrimeState c) t +
        (2000 / 47 : ℝ) * (fourPrimeError c : ℝ) * Real.log ((n : ℝ) / 10) / n) :=
      Finset.sum_le_sum (fun c _ => cdfStateLowCount_le_state_add_error hn c ht)
    _ = _ := by
      rw [Finset.sum_add_distrib, cdfStateReal_sum_eq]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, heSum]
      ring

/-- The actual odd-totient CDF lies below the certified minimum envelope, with explicit discrepancy. -/
theorem totientCdf_le_envelope_add_error {n : ℕ} (hn : 13 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    totientCdf n t ≤ cdfBoundReal t +
      (81000 / 47 : ℝ) * Real.log ((n : ℝ) / 10) / n := by
  have hstate := totientCdf_le_state_sum_add_error hn ht
  have hmoment : totientCdf n t ≤ 22 * t ^ 6 :=
    (odd_totient_cdf_lt_twenty_two_real_uniform (by omega : 0 < n) ht).le
  have hlog : 0 ≤ Real.log ((n : ℝ) / 10) := le_trans (by norm_num) (cdf_log_prefix_lower hn)
  have herr : 0 ≤ (81000 / 47 : ℝ) * Real.log ((n : ℝ) / 10) / n := by positivity
  unfold cdfBoundReal
  rw [← min_add_add_right]
  exact le_min (le_add_of_le_of_nonneg hmoment herr) hstate

#print axioms cdf_rational_le_log
#print axioms cdf_log_prefix_lower
#print axioms cdfStateLowCount_le_state_add_error
#print axioms totientCdf_eq_sum_states
#print axioms totientCdf_le_state_sum_add_error
#print axioms totientCdf_le_envelope_add_error
end Erdos883Verified
