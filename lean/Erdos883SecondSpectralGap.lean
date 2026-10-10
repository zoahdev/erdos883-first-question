import Erdos883SecondSpectralProduct

/-!
Finite coefficient sums for the odd-prime product chain's spectral gap.
The weights are nonnegative; in a tensor expansion they will be squares of
the Fourier coefficients. No completeness or basis theorem is assumed here.
-/

namespace Erdos883.SecondSpectral

noncomputable section

theorem tensorEigenvalue_weighted_gap (F : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ)
    (hF : ∀ S ∈ F, ∀ p ∈ S, p.Prime ∧ 3 ≤ p)
    (hw : ∀ S ∈ F, 0 ≤ w S) :
    -(1 / 2 : ℝ) * (∑ S ∈ F, w S) +
      (1 / 4 : ℝ) * (∑ S ∈ F.filter (fun S => S ≠ {3}), w S)
        ≤ ∑ S ∈ F, tensorEigenvalue S * w S := by
  have hpoint : ∀ S ∈ F,
      -(1 / 2 : ℝ) * w S + (1 / 4 : ℝ) * (if S = {3} then 0 else w S)
        ≤ tensorEigenvalue S * w S := by
    intro S hS
    by_cases hs : S = {3}
    · subst S
      simp [tensorEigenvalue_singleton_three]
    · have h := mul_le_mul_of_nonneg_right
        (tensorEigenvalue_ge_quarter S hs (hF S hS)) (hw S hS)
      simp only [if_neg hs]
      nlinarith [h]
  have hfilter : (∑ S ∈ F.filter (fun S => S ≠ {3}), w S) =
      ∑ S ∈ F, (if S = {3} then 0 else w S) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hs : S = {3} <;> simp [hs]
  have hsum := Finset.sum_le_sum hpoint
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← hfilter] using hsum

theorem tensorEigenvalue_weighted_square_gap (F : Finset (Finset ℕ))
    (a : Finset ℕ → ℝ)
    (hF : ∀ S ∈ F, ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    -(1 / 2 : ℝ) * (∑ S ∈ F, (a S)^2) +
      (1 / 4 : ℝ) * (∑ S ∈ F.filter (fun S => S ≠ {3}), (a S)^2)
        ≤ ∑ S ∈ F, tensorEigenvalue S * (a S)^2 :=
  tensorEigenvalue_weighted_gap F (fun S => (a S)^2) hF (fun _ _ => sq_nonneg _)

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorEigenvalue_weighted_gap
#print axioms Erdos883.SecondSpectral.tensorEigenvalue_weighted_square_gap
