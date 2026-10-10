import Erdos883SecondSpectralPair
import Erdos883SecondSpectralGap
import Erdos883SecondStabilityBounds

/-!
The finite odd-prime spectral inequality for actual functions, rather than
an assumed collection of Fourier weights. The prime labels are injective;
this is essential for the unique exceptional support {3}.
-/

namespace Erdos883.SecondSpectral

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroBits : ι → Bool := fun _ => false

def primeBitSupport (q : ι → ℕ) (s : ι → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i => s i = true)).image q

def tensorMean (p : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ x : ι → Bool, tensorWeight p x * f x

def tensorSecondMoment (p : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ x : ι → Bool, tensorWeight p x * (f x)^2

def tensorFractionalDefect (p : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  tensorMean p f - tensorSecondMoment p f

def tensorResidual (q : ι → ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : ι → Bool =>
      s ≠ zeroBits ∧ primeBitSupport q s ≠ {3}),
    (tensorFourierCoefficient (fun i => (q i : ℝ)) f s)^2 *
      tensorNorm (fun i => (q i : ℝ)) s

omit [DecidableEq ι] in
@[simp] theorem tensorBasis_zeroBits (p : ι → ℝ) (x : ι → Bool) :
    tensorBasis p zeroBits x = 1 := by
  simp [tensorBasis, zeroBits, coordinateBasis]

omit [DecidableEq ι] in
@[simp] theorem tensorNorm_zeroBits (p : ι → ℝ) :
    tensorNorm p (zeroBits : ι → Bool) = 1 := by
  simp [tensorNorm, zeroBits, coordinateNorm]

omit [DecidableEq ι] in
@[simp] theorem tensorBitEigenvalue_zeroBits (p : ι → ℝ) :
    tensorBitEigenvalue p (zeroBits : ι → Bool) = 1 := by
  simp [tensorBitEigenvalue, zeroBits, coordinateBitEigenvalue]

@[simp] theorem tensorFourierCoefficient_zeroBits (p : ι → ℝ)
    (f : (ι → Bool) → ℝ) :
    tensorFourierCoefficient p f zeroBits = tensorMean p f := by
  simp [tensorFourierCoefficient, tensorMean]

omit [DecidableEq ι] in
theorem tensorBitEigenvalue_primeSupport (q : ι → ℕ)
    (hq : Function.Injective q) (s : ι → Bool) :
    tensorBitEigenvalue (fun i => (q i : ℝ)) s =
      tensorEigenvalue (primeBitSupport q s) := by
  rw [tensorEigenvalue, primeBitSupport, Finset.prod_image hq.injOn,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [coordinateBitEigenvalue]

omit [DecidableEq ι] in
theorem tensorWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 1 ≤ p i)
    (x : ι → Bool) : 0 ≤ tensorWeight p x := by
  apply Finset.prod_nonneg
  intro i _
  cases x i <;> simp only [coordinateWeight]
  · exact div_nonneg (by linarith [hp i]) (by linarith [hp i])
  · exact div_nonneg (by norm_num) (by linarith [hp i])

omit [DecidableEq ι] in
theorem tensorNorm_nonneg (p : ι → ℝ) (hp : ∀ i, 1 ≤ p i)
    (s : ι → Bool) : 0 ≤ tensorNorm p s := by
  apply Finset.prod_nonneg
  intro i _
  cases s i <;> simp only [coordinateNorm, Bool.false_eq_true, if_false, if_true]
  · norm_num
  · exact div_nonneg (by linarith [hp i]) (sq_nonneg _)

 theorem tensorWeight_sum (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) :
    (∑ x : ι → Bool, tensorWeight p x) = 1 := by
  simp only [tensorWeight]
  rw [← Fintype.prod_sum]
  have hcoord : ∀ i, (∑ b : Bool, coordinateWeight (p i) b) = 1 := by
    intro i
    simp [Fintype.univ_bool, coordinateWeight]
    field_simp [hp i]
    ring
  simp_rw [hcoord]
  simp

 theorem tensorFractionalDefect_nonneg (p : ι → ℝ)
    (hp : ∀ i, 1 ≤ p i) (f : (ι → Bool) → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ tensorFractionalDefect p f := by
  have hle : tensorSecondMoment p f ≤ tensorMean p f := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (tensorWeight_nonneg p hp x)
    nlinarith [hf x]
  exact sub_nonneg.mpr hle

 theorem tensorResidual_nonneg (q : ι → ℕ)
    (hq : ∀ i, 3 ≤ q i) (f : (ι → Bool) → ℝ) :
    0 ≤ tensorResidual q f := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (sq_nonneg _) (tensorNorm_nonneg _
    (fun i => by exact_mod_cast (Nat.le_trans (by norm_num) (hq i))) s)

 theorem tensorPairCorrelation_spectral_gap (q : ι → ℕ)
    (hqi : Function.Injective q)
    (hq : ∀ i, (q i).Prime ∧ 3 ≤ q i)
    (f : (ι → Bool) → ℝ) :
    tensorMean (fun i => (q i : ℝ)) f *
        (3 * tensorMean (fun i => (q i : ℝ)) f - 1) / 2 +
      tensorFractionalDefect (fun i => (q i : ℝ)) f / 2 +
      tensorResidual q f / 4 ≤
        tensorPairCorrelation (fun i => (q i : ℝ)) f f := by
  let p : ι → ℝ := fun i => (q i : ℝ)
  let w : (ι → Bool) → ℝ := fun s =>
    (tensorFourierCoefficient p f s)^2 * tensorNorm p s
  have hp0 : ∀ i, p i ≠ 0 := by
    intro i
    have hh : 3 ≤ p i := by
      dsimp [p]
      exact_mod_cast (hq i).2
    linarith
  have hp1 : ∀ i, p i ≠ 1 := by
    intro i
    have hh : 3 ≤ p i := by
      dsimp [p]
      exact_mod_cast (hq i).2
    linarith
  have hp : ∀ i, 1 ≤ p i := by
    intro i
    have hh : 3 ≤ p i := by
      dsimp [p]
      exact_mod_cast (hq i).2
    linarith
  have hw : ∀ s, 0 ≤ w s := fun s =>
    mul_nonneg (sq_nonneg _) (tensorNorm_nonneg p hp s)
  have hsupport : ∀ s, ∀ r ∈ primeBitSupport q s, r.Prime ∧ 3 ≤ r := by
    intro s r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hq i
  have hpoint : ∀ s : ι → Bool,
      -(1 / 2 : ℝ) * w s +
        (3 / 2 : ℝ) * (if s = zeroBits then w s else 0) +
        (1 / 4 : ℝ) *
          (if s ≠ zeroBits ∧ primeBitSupport q s ≠ {3} then w s else 0) ≤
      tensorBitEigenvalue p s * w s := by
    intro s
    by_cases hs : s = zeroBits
    · subst s
      simp
      ring_nf
      exact le_rfl
    · have heq := tensorBitEigenvalue_primeSupport q hqi s
      have hhalf : -(1 / 2 : ℝ) ≤ tensorBitEigenvalue p s := by
        rw [heq]
        exact tensorEigenvalue_ge_half _ (fun r hr => (hsupport s r hr).2)
      by_cases h3 : primeBitSupport q s = {3}
      · simp [hs, h3]
        simpa using mul_le_mul_of_nonneg_right hhalf (hw s)
      · have hquarter : -(1 / 4 : ℝ) ≤ tensorBitEigenvalue p s := by
          rw [heq]
          exact tensorEigenvalue_ge_quarter _ h3 (hsupport s)
        simp [hs, h3]
        nlinarith [mul_le_mul_of_nonneg_right hquarter (hw s)]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (ι → Bool))) => hpoint s)
  have hzero : (∑ s : ι → Bool, if s = zeroBits then w s else 0) = w zeroBits := by
    simp
  have hres : (∑ s : ι → Bool,
      if s ≠ zeroBits ∧ primeBitSupport q s ≠ {3} then w s else 0) =
      tensorResidual q f := by
    rw [tensorResidual, Finset.sum_filter]
  have hparseval : (∑ s : ι → Bool, w s) = tensorSecondMoment p f :=
    (tensorFourier_parseval p hp0 hp1 f).symm
  have hpair : (∑ s : ι → Bool, tensorBitEigenvalue p s * w s) =
      tensorPairCorrelation p f f := by
    rw [tensorPairCorrelation_fourier p hp0 hp1]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [w]
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, hres,
    hparseval, hpair] at hsum
  have hwzero : w zeroBits = (tensorMean p f)^2 := by simp [w]
  rw [hwzero] at hsum
  dsimp [tensorFractionalDefect]
  nlinarith [hsum]

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorPairCorrelation_spectral_gap
#print axioms Erdos883.SecondSpectral.tensorFractionalDefect_nonneg
#print axioms Erdos883.SecondSpectral.tensorResidual_nonneg


