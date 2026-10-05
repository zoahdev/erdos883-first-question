import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos883Verified.Improved

/-- Part IV, high-profile large-rank branch, with exact rational constants.
The variable `h` is the transition count divided by `m`. -/
theorem high_profile_rank_budget {R β x ε h : ℝ}
    (hxlo : (1 : ℝ) / 20 ≤ x) (hxhi : x ≤ 1)
    (hε : ε < (101 : ℝ) / 5000) (hh : h < (269 : ℝ) / 10000)
    (hR : R < β + x + ε - (7074 : ℝ) / 12500) :
    2 * max 0 (R - β) + h < x := by
  by_cases hlow : R - β ≤ 0
  · rw [max_eq_left hlow]
    linarith
  · rw [max_eq_right (le_of_not_ge hlow)]
    linarith

/-- The low-profile branch polynomial is negative throughout the required interval.
An elementary split at `1/10` avoids differentiation or convexity hypotheses. -/
theorem low_profile_polynomial_negative {y : ℝ}
    (hylo : (1 : ℝ) / 20 ≤ y) (hyhi : y ≤ 1) :
    (171 : ℝ) / 500 * y ^ 6 - y + (471 : ℝ) / 10000 < 0 := by
  have hy0 : 0 ≤ y := by linarith
  by_cases hsmall : y ≤ (1 : ℝ) / 10
  · have hp := pow_le_pow_left₀ hy0 hsmall 6
    norm_num at hp
    linarith
  · have hp5 : y ^ 5 ≤ 1 := pow_le_one₀ hy0 hyhi
    have hp6 : y ^ 6 ≤ y := by
      calc
        y ^ 6 = y * y ^ 5 := by ring
        _ ≤ y * 1 := mul_le_mul_of_nonneg_left hp5 hy0
        _ = y := mul_one y
    linarith

/-- Part IV, low-profile large-rank branch. There is no additive error in its
sixth-moment hypothesis. -/
theorem low_profile_rank_budget {R β x ε h : ℝ}
    (hβ : 0 ≤ β) (hx : (1 : ℝ) / 20 ≤ x)
    (hε : ε < (101 : ℝ) / 5000) (hh : h < (269 : ℝ) / 10000)
    (hylo : (1 : ℝ) / 20 ≤ β + x + ε) (hyhi : β + x + ε ≤ 1)
    (hR : R < (171 : ℝ) / 1000 * (β + x + ε) ^ 6) :
    2 * max 0 (R - β) + h < x := by
  have hpoly := low_profile_polynomial_negative hylo hyhi
  by_cases hlow : R - β ≤ 0
  · rw [max_eq_left hlow]
    linarith
  · rw [max_eq_right (le_of_not_ge hlow)]
    linarith

/-- The clipping of `β` at 2 preserves the strict low-profile deficit. -/
theorem clipped_low_rank_profile_lt {R β β₀ : ℝ}
    (hclip : β₀ ≤ β) (hR : R < β₀ - (371 : ℝ) / 50000) : R < β := by
  linarith

/-- When the missing-even ratio exceeds the rank ratio, the cubic moment
bound lies below the missing-even ratio. -/
theorem small_rank_profile_lt_of_rank_le_missing {R β x : ℝ}
    (_hβ : 0 ≤ β) (hx : 0 < x) (hz : β + x < (3 : ℝ) / 20)
    (hxβ : x ≤ β) (hR : R < (71 : ℝ) / 25 * (β + x) ^ 3) : R < β := by
  have hz0 : 0 < β + x := by linarith
  have hp2 := pow_le_pow_left₀ hz0.le hz.le 2
  norm_num at hp2
  have hc : (142 : ℝ) / 25 * (β + x) ^ 2 < 1 := by linarith
  have hp3 := mul_lt_mul_of_pos_right hc hz0
  nlinarith

/-- When the rank ratio exceeds the missing-even ratio, the cubic moment
bound consumes less than half the rank budget. -/
theorem small_rank_twice_profile_lt_of_missing_lt_rank {R β x : ℝ}
    (hβ : 0 ≤ β) (hx : 0 < x) (hxhi : x ≤ (1 : ℝ) / 20)
    (hβx : β < x) (hR : R < (71 : ℝ) / 25 * (β + x) ^ 3) : 2 * R < x := by
  have hz0 : 0 ≤ β + x := by linarith
  have hp3 := pow_le_pow_left₀ hz0 (show β + x ≤ 2 * x by linarith) 3
  have hp2 := pow_le_pow_left₀ hx.le hxhi 2
  norm_num at hp2
  have hc : (1136 : ℝ) / 25 * x ^ 2 < 1 := by linarith
  have hx3 := mul_lt_mul_of_pos_right hc hx
  nlinarith

/-- Part IV, small-rank/few-missing-evens branch. This uses no signature
transition budget, because the product-density estimate is unstructured. -/
theorem small_rank_cubic_budget {R β x : ℝ}
    (hβ : 0 ≤ β) (hx : 0 < x) (hxhi : x ≤ (1 : ℝ) / 20)
    (hz : β + x < (3 : ℝ) / 20)
    (hR : R < (71 : ℝ) / 25 * (β + x) ^ 3) :
    2 * max 0 (R - β) < x := by
  by_cases hxβ : x ≤ β
  · have hlt := small_rank_profile_lt_of_rank_le_missing hβ hx hz hxβ hR
    rw [max_eq_left (by linarith : R - β ≤ 0)]
    linarith
  · have hlt := small_rank_twice_profile_lt_of_missing_lt_rank hβ hx hxhi
      (lt_of_not_ge hxβ) hR
    by_cases hlow : R - β ≤ 0
    · rw [max_eq_left hlow]
      linarith
    · rw [max_eq_right (le_of_not_ge hlow)]
      linarith

/-- The chosen large-rank threshold. -/
noncomputable def largeRankThreshold (β x ε : ℝ) : ℝ :=
  min ((β + x + ε) / ((27 : ℝ) / 10)) ((3 + x + ε) / ((27 : ℝ) / 5))

/-- The threshold is positive and lies in the finite CDF certificate's range. -/
theorem largeRankThreshold_bounds {β x ε : ℝ}
    (hβ : 0 ≤ β) (hx : 0 < x) (hxhi : x ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε < (101 : ℝ) / 5000) :
    0 < largeRankThreshold β x ε ∧ largeRankThreshold β x ε < (3 : ℝ) / 4 := by
  constructor
  · unfold largeRankThreshold
    apply lt_min <;> positivity
  · have ht := min_le_right ((β + x + ε) / ((27 : ℝ) / 10))
        ((3 + x + ε) / ((27 : ℝ) / 5))
    unfold largeRankThreshold
    linarith

/-- Below `10/27`, the first branch of the minimum is forced. -/
theorem largeRankThreshold_low_eq {β x ε : ℝ} (hx : 0 ≤ x) (hε : 0 ≤ ε)
    (ht : largeRankThreshold β x ε < (10 : ℝ) / 27) :
    largeRankThreshold β x ε = (β + x + ε) / ((27 : ℝ) / 10) := by
  unfold largeRankThreshold at *
  apply min_eq_left
  by_contra h
  rw [min_eq_right (le_of_not_ge h)] at ht
  linarith

/-- Whichever branch is minimal supplies one of the two required neighbor
resources. `m * ε = δ + 2` is the cleared-denominator definition of epsilon. -/
theorem largeRankThreshold_resource_target {m β x ε δ b j D : ℝ}
    (hβ : m * β = b) (hx : m * x = j) (hε : m * ε = δ + 2)
    (hD : D ≤ 3 * m + 2) :
    b + j ≤ (27 : ℝ) / 10 * m * largeRankThreshold β x ε - δ ∨
      D + j ≤ (27 : ℝ) / 5 * m * largeRankThreshold β x ε - δ := by
  unfold largeRankThreshold
  by_cases h : (β + x + ε) / ((27 : ℝ) / 10) ≤
      (3 + x + ε) / ((27 : ℝ) / 5)
  · rw [min_eq_left h]
    left
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    right
    nlinarith

/-- Conversion from the finite high-profile CDF estimate to the normalized
low-profile count used by `high_profile_rank_budget`. -/
theorem high_profile_normalized_count {R G t β x ε : ℝ}
    (hG : G < (9 : ℝ) / 10 * t - (1 : ℝ) / 6 - (11 : ℝ) / 500)
    (hR : R < 3 * G + (1 : ℝ) / 12500)
    (ht : t ≤ (β + x + ε) / ((27 : ℝ) / 10)) :
    R < β + x + ε - (7074 : ℝ) / 12500 := by
  linarith

/-- The sixth-moment coefficient in the low-profile branch is strictly
smaller than `171/1000`. -/
theorem low_profile_moment_coefficient {y : ℝ} (hy : 0 < y) :
    (66003 : ℝ) / 1000 * (y / ((27 : ℝ) / 10)) ^ 6 <
      (171 : ℝ) / 1000 * y ^ 6 := by
  have hp := pow_pos hy 6
  norm_num [div_pow]
  nlinarith

/-- The cubic coefficient for the unstructured small-rank branch. -/
theorem small_rank_moment_coefficient {z : ℝ} (hz : 0 < z) :
    (66003 : ℝ) / 1000 * ((7 : ℝ) / 20 * z) ^ 3 <
      (71 : ℝ) / 25 * z ^ 3 := by
  have hp := pow_pos hz 3
  nlinarith

/-- The CDF estimate at a clipped low-rank threshold gives the required
strict deficit in the count. -/
theorem clipped_low_rank_normalized_count {R G β₀ : ℝ}
    (hG : G < β₀ / 3 - (1 : ℝ) / 400)
    (hR : R < 3 * G + (1 : ℝ) / 12500) :
    R < β₀ - (371 : ℝ) / 50000 := by
  linarith

/-- The low-threshold branch lies exactly in the polynomial interval. -/
theorem largeRankThreshold_low_profile_interval {β x ε : ℝ}
    (hβ : 0 ≤ β) (hx : (1 : ℝ) / 20 ≤ x) (hε : 0 ≤ ε)
    (ht : largeRankThreshold β x ε < (10 : ℝ) / 27) :
    (1 : ℝ) / 20 ≤ β + x + ε ∧ β + x + ε < 1 := by
  have heq := largeRankThreshold_low_eq (show 0 ≤ x by linarith) hε ht
  constructor <;> linarith

/-- Clipping can lose at most one even vertex, and the `9/125` slack
still exceeds the rank plus discrepancy allowance. -/
theorem clipped_low_rank_resource_target {m β β₀ x δ b j : ℝ}
    (hm : 0 ≤ m) (hβ : m * β = b) (hx : m * x = j)
    (hxhi : x ≤ (1 : ℝ) / 20) (hclip : m * (β - β₀) ≤ 1)
    (hδ : δ + 2 < (101 : ℝ) / 5000 * m) :
    b + j < m * (β₀ + (9 : ℝ) / 125) - δ := by
  have hj := mul_le_mul_of_nonneg_left hxhi hm
  nlinarith

/-- The small-rank product threshold has sufficient even resources whenever
the discrepancy is below one twentieth of `b+j`. -/
theorem small_rank_resource_target {m β x t δ b j : ℝ}
    (hβ : m * β = b) (hx : m * x = j)
    (ht : t ^ 2 = (7 : ℝ) / 20 * (β + x))
    (hδ : δ < (b + j) / 20) :
    b + j < 3 * m * t ^ 2 - δ := by
  have heq := congrArg (fun z : ℝ => m * z) ht
  nlinarith

/-- Passing from normalized real counts to the exact natural-number budget
uses natural subtraction, hence exactly the positive part in the analytic bound. -/
theorem normalized_rank_budget_to_nat {R b h j m : ℕ} (hm : 0 < m)
    (hbudget : 2 * max 0 ((R : ℝ) / m - (b : ℝ) / m) + (h : ℝ) / m <
      (j : ℝ) / m) :
    2 * (R - b) + h < j := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hident : ((2 : ℝ) * (R - b : ℕ) + h) / m =
      2 * max 0 ((R : ℝ) / m - (b : ℝ) / m) + (h : ℝ) / m := by
    by_cases hbR : b ≤ R
    · have hbRreal : (b : ℝ) ≤ R := by exact_mod_cast hbR
      have hd : 0 ≤ (R : ℝ) / m - (b : ℝ) / m :=
        sub_nonneg.mpr (div_le_div_of_nonneg_right hbRreal hmreal.le)
      rw [Nat.cast_sub hbR, max_eq_right hd]
      ring
    · have hRb : R ≤ b := by omega
      have hRbreal : (R : ℝ) ≤ b := by exact_mod_cast hRb
      have hd : (R : ℝ) / m - (b : ℝ) / m ≤ 0 :=
        sub_nonpos.mpr (div_le_div_of_nonneg_right hRbreal hmreal.le)
      rw [Nat.sub_eq_zero_of_le hRb, max_eq_left hd]
      simp
  rw [← hident] at hbudget
  have hscaled := (div_lt_div_iff_of_pos_right hmreal).mp hbudget
  exact_mod_cast hscaled

#print axioms high_profile_rank_budget
#print axioms low_profile_polynomial_negative
#print axioms low_profile_rank_budget
#print axioms clipped_low_rank_profile_lt
#print axioms small_rank_profile_lt_of_rank_le_missing
#print axioms small_rank_twice_profile_lt_of_missing_lt_rank
#print axioms small_rank_cubic_budget
#print axioms largeRankThreshold_bounds
#print axioms largeRankThreshold_low_eq
#print axioms largeRankThreshold_resource_target

#print axioms high_profile_normalized_count
#print axioms low_profile_moment_coefficient
#print axioms small_rank_moment_coefficient
#print axioms clipped_low_rank_normalized_count
#print axioms largeRankThreshold_low_profile_interval
#print axioms clipped_low_rank_resource_target
#print axioms small_rank_resource_target
#print axioms normalized_rank_budget_to_nat

end Erdos883Verified.Improved
