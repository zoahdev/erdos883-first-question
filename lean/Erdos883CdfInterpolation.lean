import CdfCertificates
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos883Verified

/-- The real-valued finite-state envelope, independent of any totient CDF interpretation. -/
noncomputable def cdfStateReal (aq : Rat × Rat) (t : ℝ) : ℝ :=
  if (aq.1 : ℝ) ≤ t then (aq.2 : ℝ)
  else (aq.2 : ℝ) * min 1 ((47 : ℝ) / 2000 * ((aq.1 : ℝ) + t) /
    (2 * ((aq.1 : ℝ) - t)))

noncomputable def cdfBoundReal (t : ℝ) : ℝ :=
  min (22 * t ^ 6) ((states.map (fun aq => cdfStateReal aq t)).foldl (· + ·) 0)

private theorem rat_foldl_add_cast (L : List Rat) (q : Rat) :
    ((L.foldl (· + ·) q : Rat) : ℝ) =
      (L.map (fun r : Rat => (r : ℝ))).foldl (· + ·) (q : ℝ) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih => simp only [List.foldl_cons, List.map_cons, ih, Rat.cast_add]

/-- At every rational argument, the real envelope is exactly the cast of the certificate expression. -/
theorem cdfBoundReal_rat (t : Rat) : cdfBoundReal (t : ℝ) = (cdfBound t : ℝ) := by
  unfold cdfBoundReal cdfBound
  rw [Rat.cast_min, Rat.cast_mul, Rat.cast_pow, rat_foldl_add_cast]
  norm_num only [Rat.cast_ofNat, Rat.cast_zero]
  congr 1
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro aq haq
  simp only [Function.comp_apply, cdfStateReal, Rat.cast_le]
  split_ifs <;> simp only [Rat.cast_mul, Rat.cast_min, Rat.cast_div, Rat.cast_add,
    Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one]

private theorem states_nonnegative :
    ∀ aq ∈ states, (0 : Rat) ≤ aq.1 ∧ (0 : Rat) ≤ aq.2 := by
  decide +kernel

private theorem cdfStateReal_mono {aq : Rat × Rat}
    (ha : (0 : Rat) ≤ aq.1) (hq : (0 : Rat) ≤ aq.2)
    {x y : ℝ} (_hx : 0 ≤ x) (hxy : x ≤ y) :
    cdfStateReal aq x ≤ cdfStateReal aq y := by
  have ha' : (0 : ℝ) ≤ aq.1 := by exact_mod_cast ha
  have hq' : (0 : ℝ) ≤ aq.2 := by exact_mod_cast hq
  unfold cdfStateReal
  by_cases hax : (aq.1 : ℝ) ≤ x
  · rw [if_pos hax, if_pos (hax.trans hxy)]
  by_cases hay : (aq.1 : ℝ) ≤ y
  · rw [if_neg hax, if_pos hay]
    exact (mul_le_mul_of_nonneg_left (min_le_left 1 _) hq').trans_eq (mul_one _)
  rw [if_neg hax, if_neg hay]
  apply mul_le_mul_of_nonneg_left _ hq'
  apply min_le_min_left
  apply (div_le_div_iff₀ (by linarith : 0 < 2 * ((aq.1 : ℝ) - x))
    (by linarith : 0 < 2 * ((aq.1 : ℝ) - y))).2
  nlinarith [mul_nonneg ha' (sub_nonneg.mpr hxy)]

private theorem cdf_fold_mono (L : List (Rat × Rat))
    (hL : ∀ aq ∈ L, (0 : Rat) ≤ aq.1 ∧ (0 : Rat) ≤ aq.2)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (b c : ℝ) (hbc : b ≤ c) :
    ((L.map (fun aq => cdfStateReal aq x)).foldl (· + ·) b) ≤
      ((L.map (fun aq => cdfStateReal aq y)).foldl (· + ·) c) := by
  induction L generalizing b c with
  | nil => exact hbc
  | cons aq L ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun z hz => hL z (List.mem_cons_of_mem aq hz))
    exact add_le_add hbc (cdfStateReal_mono (hL aq (by simp)).1
      (hL aq (by simp)).2 hx hxy)

/-- The envelope is monotone on the nonnegative real axis. -/
theorem cdfBoundReal_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    cdfBoundReal x ≤ cdfBoundReal y := by
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 6) (by norm_num)
  · exact cdf_fold_mono states states_nonnegative hx hxy 0 0 le_rfl

/-- The last cell is closed at its right endpoint, obtained by clipping the floor index. -/
private theorem closed_grid_cover (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∃ i : ℕ, i < n ∧ (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
  let i := min ⌊x⌋₊ (n - 1)
  have hi : i < n := lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hn (by omega))
  refine ⟨i, hi, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast Nat.min_le_left ⌊x⌋₊ (n - 1)) (Nat.floor_le hx)
  · by_cases h : ⌊x⌋₊ ≤ n - 1
    · simpa only [i, min_eq_left h] using (Nat.lt_floor_add_one x).le
    · have hi' : i = n - 1 := min_eq_right (by omega)
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
      have hnR : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn'
      rw [hi', hnR]
      exact hxn

/-- The 1000 exact high-cell certificates bound the envelope throughout the real interval. -/
theorem cdfBoundReal_high {t : ℝ} (hlo : 1 / 3 ≤ t) (hhi : t ≤ 3 / 4) :
    cdfBoundReal t < (9 / 10) * t - 1 / 6 - 29 / 1000 := by
  obtain ⟨i, hi, hil, hir⟩ := closed_grid_cover 1000 (by omega)
    (2400 * (t - 1 / 3)) (by linarith) (by norm_num; linarith)
  have hleft : (1 : ℝ) / 3 + (i : ℝ) / 2400 ≤ t := by linarith
  have hright : t ≤ (1 : ℝ) / 3 + ((i + 1 : ℕ) : ℝ) / 2400 := by
    push_cast
    linarith
  have hcert := high_cells ⟨i, hi⟩
  unfold highCell at hcert
  have hcertR : (9 : ℝ) / 10 * (1 / 3 + (i : ℝ) / 2400) - 1 / 6 -
      (cdfBound (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) : ℝ) > 29 / 1000 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hcert
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_add,
      Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast, Fin.val_mk] at h
    exact h
  have heq : cdfBoundReal (1 / 3 + ((i + 1 : ℕ) : ℝ) / 2400) =
      (cdfBound (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) : ℝ) := by
    convert cdfBoundReal_rat (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) using 1
    push_cast
    rfl
  have hmono := cdfBoundReal_mono (by linarith : 0 ≤ t) hright
  rw [heq] at hmono
  linarith

/-- Exact upper square-root witnesses and the 1910 low cells give the second real interval bound. -/
theorem cdfBoundReal_low {β : ℝ} (hlo : 1 / 10 ≤ β) (hhi : β ≤ 201 / 100) :
    cdfBoundReal (Real.sqrt ((β + 3 / 100) / 3)) < β / 3 - 119 / 5000 := by
  obtain ⟨i, hi, hil, hir⟩ := closed_grid_cover 1910 (by omega)
    (1000 * (β - 1 / 10)) (by linarith) (by norm_num; linarith)
  have hleft : (1 : ℝ) / 10 + (i : ℝ) / 1000 ≤ β := by linarith
  have hright : β ≤ (1 : ℝ) / 10 + ((i + 1 : ℕ) : ℝ) / 1000 := by
    push_cast
    linarith
  let q : Rat := (lowSqrtWitnesses[i]?.getD 0 : Rat) / 1000000000
  have hcert := low_cells ⟨i, hi⟩
  change (1 / 10 + ((i + 1 : ℕ) : Rat) / 1000 + 3 / 100) / 3 ≤ q ^ 2 ∧
    0 ≤ q ∧ (1 / 10 + (i : Rat) / 1000) / 3 - cdfBound q > 119 / 5000 at hcert
  have hsq : ((1 : ℝ) / 10 + ((i + 1 : ℕ) : ℝ) / 1000 + 3 / 100) / 3 ≤
      (q : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hcert.1
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast] at h
    exact h
  have hq : (0 : ℝ) ≤ q := by exact_mod_cast hcert.2.1
  have hsqrt : Real.sqrt ((β + 3 / 100) / 3) ≤ (q : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hq, le_trans (by linarith) hsq⟩
  have hgap : ((1 : ℝ) / 10 + (i : ℝ) / 1000) / 3 - (cdfBound q : ℝ) >
      119 / 5000 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hcert.2.2
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast] at h
    exact h
  have hmono := cdfBoundReal_mono (Real.sqrt_nonneg _) hsqrt
  rw [cdfBoundReal_rat] at hmono
  linarith

#print axioms cdfBoundReal_rat
#print axioms cdfBoundReal_mono
#print axioms cdfBoundReal_high
#print axioms cdfBoundReal_low
end Erdos883Verified
