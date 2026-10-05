import Arithmetic
import Erdos883FiniteTailThresholds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Erdos883Verified.Improved

/-- The principal half-length is positive throughout the analytic range. -/
theorem large_m_pos {n : ℕ} (hn : 200000 ≤ n) : 0 < n / 6 := by omega

/-- Division by six, with its exact integer remainder allowance. -/
theorem large_m_floor_bounds (n : ℕ) :
    6 * (n / 6) ≤ n ∧ n ≤ 6 * (n / 6) + 5 := by omega

/-- The resource cost is at most three principal half-lengths plus two. -/
theorem resource_cost_le_three_m_add_two (n : ℕ) :
    n - threshold n + n / 6 ≤ 3 * (n / 6) + 2 := by
  unfold threshold
  omega

/-- The supply of even vertices is at least three principal half-lengths. -/
theorem three_m_le_half (n : ℕ) : 3 * (n / 6) ≤ n / 2 := by omega

/-- The supply of odd vertices has a uniform three-unit rounding allowance. -/
theorem halfOdds_le_three_m_add_three (n : ℕ) :
    halfOdds n ≤ 3 * (n / 6) + 3 := by
  unfold halfOdds
  omega

/-- The count removed from the odd side has a one-unit rounding allowance. -/
theorem missing_odds_le_two_m_add_one (n : ℕ) :
    halfOdds n - retainedOdds n ≤ 2 * (n / 6) + 1 := by
  unfold halfOdds retainedOdds
  omega

theorem b_le_two_m_add_one {n b : ℕ} (hb : b ≤ halfOdds n - retainedOdds n) :
    b ≤ 2 * (n / 6) + 1 := hb.trans (missing_odds_le_two_m_add_one n)

/-- The normalized ambient size, with the manuscript's exact rational constant. -/
theorem large_n_div_two_m_lt {n : ℕ} (hn : 200000 ≤ n) :
    (n : ℝ) / (2 * (n / 6 : ℕ)) < (37501 : ℝ) / 12500 := by
  have hm : (33333 : ℝ) ≤ (n / 6 : ℕ) := by exact_mod_cast (show 33333 ≤ n / 6 by omega)
  have hnm : (n : ℝ) ≤ 6 * (n / 6 : ℕ) + 5 := by
    exact_mod_cast (large_m_floor_bounds n).2
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n / 6 : ℕ))).2
  linarith

/-- The normalized twenty-twofold odd supply. -/
theorem large_twenty_two_halfOdds_div_m_lt {n : ℕ} (hn : 200000 ≤ n) :
    22 * (halfOdds n : ℝ) / (n / 6 : ℕ) < (66003 : ℝ) / 1000 := by
  have hm : (33333 : ℝ) ≤ (n / 6 : ℕ) := by exact_mod_cast (show 33333 ≤ n / 6 by omega)
  have hH : (halfOdds n : ℝ) ≤ 3 * (n / 6 : ℕ) + 3 := by
    exact_mod_cast halfOdds_le_three_m_add_three n
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n / 6 : ℕ))).2
  linarith

/-- A deliberately rounded-down square-root lower bound. -/
theorem large_sqrt_ge_447 {n : ℕ} (hn : 200000 ≤ n) :
    (447 : ℝ) ≤ Real.sqrt n := by
  have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hp := Real.sqrt_nonneg (n : ℝ)
  nlinarith

/-- An elementary quadratic estimate for the discrepancy budget. -/
theorem large_sqrt_discrepancy_polynomial {n : ℕ} (hn : 200000 ≤ n) :
    9 * Real.sqrt n + 12 < (101 : ℝ) / 5000 * ((n : ℝ) - 5) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hlo := large_sqrt_ge_447 hn
  nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 447)]

/-- An elementary quadratic estimate for the transition budget. -/
theorem large_sqrt_transition_polynomial {n : ℕ} (hn : 200000 ≤ n) :
    12 * Real.sqrt n + 6 < (269 : ℝ) / 10000 * ((n : ℝ) - 5) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hlo := large_sqrt_ge_447 hn
  nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 447)]

/-- The normalized discrepancy is strictly below 0.0202. -/
theorem large_discrepancy_div_m_lt {n : ℕ} (hn : 200000 ≤ n) :
    ((3 : ℝ) / 2 * Real.sqrt n + 2) / (n / 6 : ℕ) < (101 : ℝ) / 5000 := by
  have hm : (0 : ℝ) < (n / 6 : ℕ) := by exact_mod_cast large_m_pos hn
  have hnm : (n : ℝ) ≤ 6 * (n / 6 : ℕ) + 5 := by
    exact_mod_cast (large_m_floor_bounds n).2
  apply (div_lt_iff₀ hm).2
  have hp := large_sqrt_discrepancy_polynomial hn
  linarith

/-- Minimality of the base-four scale bounds the number of transitions by a square root. -/
theorem uniformTailScale_two_pow_lt_two_sqrt {n : ℕ} (hn : 1024 < n) :
    ((2 ^ uniformTailScale n : ℕ) : ℝ) < 2 * Real.sqrt n := by
  have hs := uniformTailScale_ge_six hn
  have hp : ((4 ^ (uniformTailScale n - 1) : ℕ) : ℝ) < n := by
    exact_mod_cast four_pow_pred_uniformTailScale_lt hn
  have heq : (((2 ^ uniformTailScale n : ℕ) : ℝ)) ^ 2 =
      4 * ((4 ^ (uniformTailScale n - 1) : ℕ) : ℝ) := by
    norm_cast
    calc
      (2 ^ uniformTailScale n) ^ 2 = 4 ^ uniformTailScale n := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      _ = 4 * 4 ^ (uniformTailScale n - 1) := by
        conv_lhs => rw [show uniformTailScale n = (uniformTailScale n - 1) + 1 by omega]
        rw [pow_succ, Nat.mul_comm]
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hnonneg := Real.sqrt_nonneg (n : ℝ)
  have hpow : (0 : ℝ) ≤ ((2 ^ uniformTailScale n : ℕ) : ℝ) := by positivity
  nlinarith

/-- The normalized number of blocks is strictly below 0.0269. -/
theorem large_transition_div_m_lt {n : ℕ} (hn : 200000 ≤ n) :
    (((2 ^ uniformTailScale n + 1 : ℕ) : ℝ)) / (n / 6 : ℕ) < (269 : ℝ) / 10000 := by
  have hm : (0 : ℝ) < (n / 6 : ℕ) := by exact_mod_cast large_m_pos hn
  have hnm : (n : ℝ) ≤ 6 * (n / 6 : ℕ) + 5 := by
    exact_mod_cast (large_m_floor_bounds n).2
  have hpow := uniformTailScale_two_pow_lt_two_sqrt (show 1024 < n by omega)
  have hp := large_sqrt_transition_polynomial hn
  apply (div_lt_iff₀ hm).2
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Clipping the normalized missing count at two loses at most one vertex. -/
theorem clipped_beta_loss {n b : ℕ} (hn : 200000 ≤ n)
    (hb : b ≤ halfOdds n - retainedOdds n) :
    0 ≤ (n / 6 : ℕ) * ((b : ℝ) / (n / 6 : ℕ) - min ((b : ℝ) / (n / 6 : ℕ)) 2) ∧
    (n / 6 : ℕ) * ((b : ℝ) / (n / 6 : ℕ) - min ((b : ℝ) / (n / 6 : ℕ)) 2) ≤ 1 := by
  have hm : (0 : ℝ) < (n / 6 : ℕ) := by exact_mod_cast large_m_pos hn
  have hbR : (b : ℝ) ≤ 2 * (n / 6 : ℕ) + 1 := by
    exact_mod_cast b_le_two_m_add_one hb
  have hcancel : (n / 6 : ℕ) * ((b : ℝ) / (n / 6 : ℕ)) = b := by
    field_simp
  by_cases hle : (b : ℝ) / (n / 6 : ℕ) ≤ 2
  · rw [min_eq_left hle]
    simp
  · rw [min_eq_right (le_of_not_ge hle)]
    constructor
    · exact mul_nonneg (le_of_lt hm) (sub_nonneg.mpr (le_of_not_ge hle))
    · nlinarith

end Erdos883Verified.Improved

#print axioms Erdos883Verified.Improved.large_n_div_two_m_lt
#print axioms Erdos883Verified.Improved.large_twenty_two_halfOdds_div_m_lt
#print axioms Erdos883Verified.Improved.large_discrepancy_div_m_lt
#print axioms Erdos883Verified.Improved.large_transition_div_m_lt
#print axioms Erdos883Verified.Improved.clipped_beta_loss
