import Erdos883SecondMomentBound

namespace Erdos883Second.Near

open Erdos883Verified

/-- Finite Markov inequality at arbitrary order for the actual prefix. -/
theorem totient_below_card_le_moment (n k : ℕ) {z : ℚ} (hz : 0 < z) :
    (((Finset.Icc 1 n).filter (fun v => totientDensity v < z)).card : ℚ) ≤
      z ^ k * ∑ v ∈ Finset.Icc 1 n, (totientDensity v)⁻¹ ^ k := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ v ∈ (Finset.Icc 1 n).filter (fun v => totientDensity v < z),
        (1 : ℚ) := by simp
    _ ≤ ∑ v ∈ (Finset.Icc 1 n).filter (fun v => totientDensity v < z),
        z ^ k * (totientDensity v)⁻¹ ^ k := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvu, hvz⟩ := Finset.mem_filter.mp hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp hvu).1
      have hrho := totientDensity_pos hvpos
      have h1 : (1 : ℚ) ≤ z * (totientDensity v)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (one_le_div hrho).mpr hvz.le
      simpa only [mul_pow] using one_le_pow₀ h1 (n := k)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v hv hvo
      exact mul_nonneg (pow_nonneg hz.le k)
        (pow_nonneg (inv_nonneg.mpr (totientDensity_nonneg v)) k)

/-- Explicit uniform bound on how many positive prefix values have low density. -/
theorem totient_below_card_le (n k : ℕ) {z : ℚ} (hz : 0 < z) :
    (((Finset.Icc 1 n).filter (fun v => totientDensity v < z)).card : ℚ) ≤
      momentConstant k * n * z ^ k := by
  calc
    _ ≤ z ^ k * ∑ v ∈ Finset.Icc 1 n, (totientDensity v)⁻¹ ^ k :=
      totient_below_card_le_moment n k hz
    _ ≤ z ^ k * (momentConstant k * n) :=
      mul_le_mul_of_nonneg_left (inverse_totient_moment_le n k)
        (pow_nonneg hz.le k)
    _ = _ := by ring

/-- A selected positive subset larger than the explicit bad-profile budget
contains a vertex with the required density. -/
theorem good_totient_in_subset {n k : ℕ} {T : Finset ℕ} {z : ℚ}
    (hT : T ⊆ Finset.Icc 1 n) (hz : 0 < z)
    (hbudget : momentConstant k * n * z ^ k < (T.card : ℚ)) :
    ∃ a ∈ T, z ≤ totientDensity a := by
  classical
  by_contra h
  push_neg at h
  have hs : T ⊆ (Finset.Icc 1 n).filter (fun v => totientDensity v < z) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨hT hv, h v hv⟩
  have hc : (T.card : ℚ) ≤
      (((Finset.Icc 1 n).filter (fun v => totientDensity v < z)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hs
  exact (not_lt_of_ge (hc.trans (totient_below_card_le n k hz))) hbudget

#print axioms totient_below_card_le
#print axioms good_totient_in_subset

end Erdos883Second.Near
