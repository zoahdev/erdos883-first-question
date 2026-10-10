import Erdos883SecondSpectralFourier
import Mathlib.Data.Fintype.BigOperators

/-!
Diagonalization of the finite disjoint-pair correlation form in the weighted
tensor coordinates. Pair states are functions to Bool × Bool; the marginals
are the two coordinate projections. This keeps the entire proof finite.
-/

namespace Erdos883.SecondSpectral

noncomputable section

def coordinatePairWeight (p : ℝ) : Bool → Bool → ℝ
  | false, false => (p - 2) / p
  | false, true => 1 / p
  | true, false => 1 / p
  | true, true => 0

def coordinateBitEigenvalue (p : ℝ) (s : Bool) : ℝ :=
  if s then coordinateEigenvalue p else 1

theorem coordinatePair_basis (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (s t : Bool) :
    (∑ b : Bool × Bool, coordinatePairWeight p b.1 b.2 *
      coordinateBasis p s b.1 * coordinateBasis p t b.2) =
        if s = t then coordinateBitEigenvalue p s * coordinateNorm p s else 0 := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  rw [Fintype.sum_prod_type]
  cases s <;> cases t <;>
    simp [Fintype.univ_bool, coordinatePairWeight, coordinateBasis,
      coordinateBitEigenvalue, coordinateNorm, coordinateEigenvalue, centeredCoordinate]
  all_goals field_simp
  all_goals ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorBitEigenvalue (p : ι → ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, coordinateBitEigenvalue (p i) (s i)

def tensorPairWeight (p : ι → ℝ) (z : ι → Bool × Bool) : ℝ :=
  ∏ i, coordinatePairWeight (p i) (z i).1 (z i).2

def tensorPairCorrelation (p : ι → ℝ) (f g : (ι → Bool) → ℝ) : ℝ :=
  ∑ z : ι → Bool × Bool, tensorPairWeight p z *
    f (fun i => (z i).1) * g (fun i => (z i).2)

theorem tensorPair_basis_product (p : ι → ℝ) (s t : ι → Bool) :
    tensorPairCorrelation p (tensorBasis p s) (tensorBasis p t) =
      ∏ i, (∑ b : Bool × Bool, coordinatePairWeight (p i) b.1 b.2 *
        coordinateBasis (p i) (s i) b.1 * coordinateBasis (p i) (t i) b.2) := by
  rw [tensorPairCorrelation, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [tensorPairWeight, tensorBasis, Finset.prod_mul_distrib]

theorem tensorPair_basis (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1) (s t : ι → Bool) :
    tensorPairCorrelation p (tensorBasis p s) (tensorBasis p t) =
      if s = t then tensorBitEigenvalue p s * tensorNorm p s else 0 := by
  rw [tensorPair_basis_product]
  simp_rw [coordinatePair_basis _ (hp0 _) (hp1 _)]
  by_cases h : s = t
  · subst t
    simp [tensorBitEigenvalue, tensorNorm, Finset.prod_mul_distrib]
  · simp only [if_neg h]
    have hall : ¬ ∀ i, s i = t i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem tensorPairCorrelation_tensorSums (p : ι → ℝ)
    (a b : (ι → Bool) → ℝ) :
    tensorPairCorrelation p
      (fun x => ∑ s : ι → Bool, a s * tensorBasis p s x)
      (fun y => ∑ t : ι → Bool, b t * tensorBasis p t y) =
        ∑ t : ι → Bool, ∑ s : ι → Bool,
          a s * b t * tensorPairCorrelation p (tensorBasis p s) (tensorBasis p t) := by
  simp only [tensorPairCorrelation, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem tensorPairCorrelation_fourier (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1)
    (f g : (ι → Bool) → ℝ) :
    tensorPairCorrelation p f g =
      ∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorFourierCoefficient p g s *
        (tensorBitEigenvalue p s * tensorNorm p s) := by
  have hf : f = fun x => ∑ s : ι → Bool,
      tensorFourierCoefficient p f s * tensorBasis p s x := by
    funext x
    exact (tensorFourier_expansion p hp0 hp1 f x).symm
  have hg : g = fun x => ∑ s : ι → Bool,
      tensorFourierCoefficient p g s * tensorBasis p s x := by
    funext x
    exact (tensorFourier_expansion p hp0 hp1 g x).symm
  calc
    tensorPairCorrelation p f g =
      tensorPairCorrelation p
        (fun x => ∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorBasis p s x)
        (fun x => ∑ s : ι → Bool, tensorFourierCoefficient p g s * tensorBasis p s x) := by
          conv_lhs => rw [hf, hg]
    _ = ∑ s : ι → Bool, ∑ t : ι → Bool,
        tensorFourierCoefficient p f s * tensorFourierCoefficient p g t *
          tensorPairCorrelation p (tensorBasis p s) (tensorBasis p t) :=
      by rw [tensorPairCorrelation_tensorSums, Finset.sum_comm]
    _ = ∑ s : ι → Bool, tensorFourierCoefficient p f s * tensorFourierCoefficient p g s *
        (tensorBitEigenvalue p s * tensorNorm p s) := by
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [tensorPair_basis p hp0 hp1]
      rw [Finset.sum_eq_single s]
      · simp
      · intro t _ ht
        simp [Ne.symm ht]
      · intro hs
        exact False.elim (hs (Finset.mem_univ s))

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorPair_basis
#print axioms Erdos883.SecondSpectral.tensorPairCorrelation_fourier
