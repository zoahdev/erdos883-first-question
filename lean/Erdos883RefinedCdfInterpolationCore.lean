import Erdos883RefinedCdfReal

namespace Erdos883Verified

/-- The last cell is closed at its right endpoint, obtained by clipping the floor index. -/
private theorem refined_closed_grid_cover (n : ℕ) (hn : 0 < n) (x : ℝ)
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
theorem refinedCdfBoundReal_high_of_cells
    (hcells : ∀ i : Fin 1000, refinedHighCell i.val) {t : ℝ} (hlo : 1 / 3 ≤ t) (hhi : t ≤ 3 / 4) :
    refinedCdfBoundReal t < (9 / 10) * t - 1 / 6 - 11 / 500 := by
  obtain ⟨i, hi, hil, hir⟩ := refined_closed_grid_cover 1000 (by omega)
    (2400 * (t - 1 / 3)) (by linarith) (by norm_num; linarith)
  have hleft : (1 : ℝ) / 3 + (i : ℝ) / 2400 ≤ t := by linarith
  have hright : t ≤ (1 : ℝ) / 3 + ((i + 1 : ℕ) : ℝ) / 2400 := by
    push_cast
    linarith
  have hcert := hcells ⟨i, hi⟩
  unfold refinedHighCell at hcert
  have hcertR : (9 : ℝ) / 10 * (1 / 3 + (i : ℝ) / 2400) - 1 / 6 -
      (refinedCdfBound (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) : ℝ) > 11 / 500 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hcert
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_add,
      Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast, Fin.val_mk] at h
    exact h
  have heq : refinedCdfBoundReal (1 / 3 + ((i + 1 : ℕ) : ℝ) / 2400) =
      (refinedCdfBound (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) : ℝ) := by
    convert refinedCdfBoundReal_rat (1 / 3 + ((i + 1 : ℕ) : Rat) / 2400) using 1
    push_cast
    rfl
  have hmono := refinedCdfBoundReal_mono (by linarith : 0 ≤ t) hright
  rw [heq] at hmono
  linarith

/-- Exact upper square-root witnesses and the 1910 low cells give the second real interval bound. -/
theorem refinedCdfBoundReal_low_of_cells
    (hcells : ∀ i : Fin 1910, refinedLowCell i.val) {β : ℝ} (hlo : 1 / 10 ≤ β) (hhi : β ≤ 201 / 100) :
    refinedCdfBoundReal (Real.sqrt ((β + 9 / 125) / 3)) < β / 3 - 1 / 400 := by
  obtain ⟨i, hi, hil, hir⟩ := refined_closed_grid_cover 1910 (by omega)
    (1000 * (β - 1 / 10)) (by linarith) (by norm_num; linarith)
  have hleft : (1 : ℝ) / 10 + (i : ℝ) / 1000 ≤ β := by linarith
  have hright : β ≤ (1 : ℝ) / 10 + ((i + 1 : ℕ) : ℝ) / 1000 := by
    push_cast
    linarith
  let q : Rat := (refinedLowSqrtWitnesses[i]?.getD 0 : Rat) / 1000000000
  have hcert := hcells ⟨i, hi⟩
  change (1 / 10 + ((i + 1 : ℕ) : Rat) / 1000 + 9 / 125) / 3 ≤ q ^ 2 ∧
    0 ≤ q ∧ (1 / 10 + (i : Rat) / 1000) / 3 - refinedCdfBound q > 1 / 400 at hcert
  have hsq : ((1 : ℝ) / 10 + ((i + 1 : ℕ) : ℝ) / 1000 + 9 / 125) / 3 ≤
      (q : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hcert.1
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast] at h
    exact h
  have hq : (0 : ℝ) ≤ q := by exact_mod_cast hcert.2.1
  have hsqrt : Real.sqrt ((β + 9 / 125) / 3) ≤ (q : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hq, le_trans (by linarith) hsq⟩
  have hgap : ((1 : ℝ) / 10 + (i : ℝ) / 1000) / 3 - (refinedCdfBound q : ℝ) >
      1 / 400 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hcert.2.2
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast] at h
    exact h
  have hmono := refinedCdfBoundReal_mono (Real.sqrt_nonneg _) hsqrt
  rw [refinedCdfBoundReal_rat] at hmono
  linarith


#print axioms refinedCdfBoundReal_high_of_cells
#print axioms refinedCdfBoundReal_low_of_cells
end Erdos883Verified
