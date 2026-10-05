import Erdos883RefinedCdfDefinitions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos883Verified

noncomputable def refinedCdfStateReal (aqe : Rat × Rat × Rat) (t : ℝ) : ℝ :=
  let cap := (aqe.2.1 : ℝ) + 2 * (aqe.2.2 : ℝ) / 200000
  let num := (aqe.2.1 : ℝ) * (47 / 2000) + (aqe.2.2 : ℝ) * (991 / 100) / 200000
  if (aqe.1 : ℝ) ≤ t then cap else min cap (num * ((aqe.1 : ℝ) + t) / (2 * ((aqe.1 : ℝ) - t)))

noncomputable def refinedCdfBoundReal (t : ℝ) : ℝ :=
  min (22 * t^6) ((refinedCdfStates.map (fun aqe => refinedCdfStateReal aqe t)).foldl (· + ·) 0)

private theorem refined_rat_foldl_add_cast (L : List Rat) (q : Rat) :
    ((L.foldl (· + ·) q : Rat) : ℝ) =
      (L.map (fun r : Rat => (r : ℝ))).foldl (· + ·) (q : ℝ) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih => simp only [List.foldl_cons, List.map_cons, ih, Rat.cast_add]

theorem refinedCdfBoundReal_rat (t : Rat) :
    refinedCdfBoundReal (t : ℝ) = (refinedCdfBound t : ℝ) := by
  unfold refinedCdfBoundReal refinedCdfBound
  rw [Rat.cast_min, Rat.cast_mul, Rat.cast_pow, refined_rat_foldl_add_cast]
  norm_num only [Rat.cast_ofNat, Rat.cast_zero]
  congr 1
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro aqe haq
  simp only [Function.comp_apply, refinedCdfStateReal, refinedCdfState, Rat.cast_le]
  split_ifs <;> simp only [Rat.cast_mul, Rat.cast_min, Rat.cast_div, Rat.cast_add,
    Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one]

private theorem refined_states_nonnegative :
    ∀ aqe ∈ refinedCdfStates,
      (0 : Rat) ≤ aqe.1 ∧ (0 : Rat) ≤ aqe.2.1 ∧ (0 : Rat) ≤ aqe.2.2 := by
  decide +kernel

private theorem refinedCdfStateReal_mono {aqe : Rat × Rat × Rat}
    (ha : (0 : Rat) ≤ aqe.1) (hq : (0 : Rat) ≤ aqe.2.1) (he : (0 : Rat) ≤ aqe.2.2)
    {x y : ℝ} (_hx : 0 ≤ x) (hxy : x ≤ y) :
    refinedCdfStateReal aqe x ≤ refinedCdfStateReal aqe y := by
  have ha' : (0 : ℝ) ≤ aqe.1 := by exact_mod_cast ha
  have hq' : (0 : ℝ) ≤ aqe.2.1 := by exact_mod_cast hq
  have he' : (0 : ℝ) ≤ aqe.2.2 := by exact_mod_cast he
  have hnum : 0 ≤ (aqe.2.1 : ℝ) * (47 / 2000) + (aqe.2.2 : ℝ) * (991 / 100) / 200000 := by positivity
  unfold refinedCdfStateReal
  dsimp only
  by_cases hax : (aqe.1 : ℝ) ≤ x
  · rw [if_pos hax, if_pos (hax.trans hxy)]
  by_cases hay : (aqe.1 : ℝ) ≤ y
  · rw [if_neg hax, if_pos hay]
    exact min_le_left _ _
  rw [if_neg hax, if_neg hay]
  apply min_le_min_left
  apply (div_le_div_iff₀ (by linarith : 0 < 2 * ((aqe.1 : ℝ) - x))
    (by linarith : 0 < 2 * ((aqe.1 : ℝ) - y))).2
  nlinarith [mul_nonneg hnum (mul_nonneg ha' (sub_nonneg.mpr hxy))]

private theorem refined_cdf_fold_mono (L : List (Rat × Rat × Rat))
    (hL : ∀ aqe ∈ L, (0 : Rat) ≤ aqe.1 ∧ (0 : Rat) ≤ aqe.2.1 ∧ (0 : Rat) ≤ aqe.2.2)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (b c : ℝ) (hbc : b ≤ c) :
    ((L.map (fun aqe => refinedCdfStateReal aqe x)).foldl (· + ·) b) ≤
      ((L.map (fun aqe => refinedCdfStateReal aqe y)).foldl (· + ·) c) := by
  induction L generalizing b c with
  | nil => exact hbc
  | cons aqe L ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun z hz => hL z (List.mem_cons_of_mem aqe hz))
    exact add_le_add hbc (refinedCdfStateReal_mono (hL aqe (by simp)).1
      (hL aqe (by simp)).2.1 (hL aqe (by simp)).2.2 hx hxy)

theorem refinedCdfBoundReal_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    refinedCdfBoundReal x ≤ refinedCdfBoundReal y := by
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 6) (by norm_num)
  · exact refined_cdf_fold_mono refinedCdfStates refined_states_nonnegative hx hxy 0 0 le_rfl

#print axioms refinedCdfBoundReal_rat
#print axioms refinedCdfBoundReal_mono
end Erdos883Verified
