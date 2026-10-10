import Erdos883SecondSpectralBasis

/-!
Exact finite Fourier expansion and Parseval identity for the weighted Bool
product space. Coordinates are unnormalized, so Parseval uses the strictly
nonzero coordinate norm products explicitly.
-/

namespace Erdos883.SecondSpectral

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorFourierCoefficient (p : ι → ℝ) (f : (ι → Bool) → ℝ)
    (s : ι → Bool) : ℝ :=
  (∑ x : ι → Bool, tensorWeight p x * f x * tensorBasis p s x) / tensorNorm p s

omit [DecidableEq ι] in
theorem tensorNorm_ne_zero (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1) (s : ι → Bool) :
    tensorNorm p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hpi : p i - 1 ≠ 0 := sub_ne_zero.mpr (hp1 i)
  cases s i <;> simp [coordinateNorm, hp0 i, hpi]

theorem tensorFourier_expansion (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1)
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorBasis p s x) = f x := by
  calc
    (∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorBasis p s x)
        = ∑ y : ι → Bool, f y * (tensorWeight p y *
            ∑ s : ι → Bool, tensorBasis p s x * tensorBasis p s y / tensorNorm p s) := by
          simp only [tensorFourierCoefficient, div_eq_mul_inv, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = ∑ y : ι → Bool, f y * (if x = y then 1 else 0) := by
      simp_rw [tensorBasis_resolution p hp0 hp1]
    _ = f x := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · intro hx
        exact False.elim (hx (Finset.mem_univ x))

theorem tensorFourier_numerator (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1)
    (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    tensorFourierCoefficient p f s * tensorNorm p s =
      ∑ x : ι → Bool, tensorWeight p x * f x * tensorBasis p s x := by
  exact div_mul_cancel₀ _ (tensorNorm_ne_zero p hp0 hp1 s)

theorem tensorFourier_parseval (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, tensorWeight p x * (f x)^2) =
      ∑ s : ι → Bool, (tensorFourierCoefficient p f s)^2 * tensorNorm p s := by
  calc
    (∑ x : ι → Bool, tensorWeight p x * (f x)^2)
        = ∑ x : ι → Bool, tensorWeight p x * f x *
            (∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorBasis p s x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [tensorFourier_expansion p hp0 hp1 f x]
          ring
    _ = ∑ s : ι → Bool, tensorFourierCoefficient p f s *
        (∑ x : ι → Bool, tensorWeight p x * f x * tensorBasis p s x) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ s : ι → Bool, (tensorFourierCoefficient p f s)^2 * tensorNorm p s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← tensorFourier_numerator p hp0 hp1 f s]
      ring

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorFourier_expansion
#print axioms Erdos883.SecondSpectral.tensorFourier_parseval
