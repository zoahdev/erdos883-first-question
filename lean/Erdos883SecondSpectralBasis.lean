import Erdos883SecondSpectralKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
An elementary finite weighted tensor family. Coordinates use the unnormalized
centered Bernoulli variable, which avoids square roots. The tensor resolution
of the identity is intended as the foundation for finite Fourier expansion.
-/

namespace Erdos883.SecondSpectral

noncomputable section

def coordinateWeight (p : ℝ) : Bool → ℝ
  | false => (p - 1) / p
  | true => 1 / p

def coordinateBasis (p : ℝ) (s : Bool) : Bool → ℝ :=
  if s then centeredCoordinate p else fun _ => 1

def coordinateNorm (p : ℝ) (s : Bool) : ℝ :=
  if s then (p - 1) / p^2 else 1

theorem coordinateBasis_inner (p : ℝ) (hp : p ≠ 0) (s t : Bool) :
    (∑ b : Bool, coordinateWeight p b * coordinateBasis p s b *
      coordinateBasis p t b) = if s = t then coordinateNorm p s else 0 := by
  cases s <;> cases t <;>
    simp [Fintype.univ_bool, coordinateWeight, coordinateBasis,
      coordinateNorm, centeredCoordinate]
  all_goals field_simp
  all_goals ring

theorem coordinateBasis_resolution (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (x y : Bool) :
    coordinateWeight p y * (∑ s : Bool,
      coordinateBasis p s x * coordinateBasis p s y / coordinateNorm p s) =
        if x = y then 1 else 0 := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  cases x <;> cases y <;>
    simp [Fintype.univ_bool, coordinateWeight, coordinateBasis,
      coordinateNorm, centeredCoordinate]
  all_goals field_simp
  all_goals simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorWeight (p : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, coordinateWeight (p i) (x i)

def tensorBasis (p : ι → ℝ) (s x : ι → Bool) : ℝ :=
  ∏ i, coordinateBasis (p i) (s i) (x i)

def tensorNorm (p : ι → ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, coordinateNorm (p i) (s i)

theorem tensorBasis_inner_product (p : ι → ℝ) (s t : ι → Bool) :
    (∑ x : ι → Bool, tensorWeight p x * tensorBasis p s x * tensorBasis p t x) =
      ∏ i, (∑ b : Bool, coordinateWeight (p i) b * coordinateBasis (p i) (s i) b *
        coordinateBasis (p i) (t i) b) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [tensorWeight, tensorBasis, Finset.prod_mul_distrib]

theorem tensorBasis_orthogonal (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (s t : ι → Bool) :
    (∑ x : ι → Bool, tensorWeight p x * tensorBasis p s x * tensorBasis p t x) =
      if s = t then tensorNorm p s else 0 := by
  rw [tensorBasis_inner_product]
  simp_rw [coordinateBasis_inner _ (hp _)]
  by_cases h : s = t
  · subst t
    simp [tensorNorm]
  · simp only [if_neg h]
    have hall : ¬ ∀ i, s i = t i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem tensorBasis_resolution_product (p : ι → ℝ) (x y : ι → Bool) :
    (∑ s : ι → Bool, tensorBasis p s x * tensorBasis p s y / tensorNorm p s) =
      ∏ i, (∑ b : Bool, coordinateBasis (p i) b (x i) *
        coordinateBasis (p i) b (y i) / coordinateNorm (p i) b) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [tensorBasis, tensorNorm, Finset.prod_div_distrib, Finset.prod_mul_distrib]

theorem tensorBasis_resolution (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i ≠ 1) (x y : ι → Bool) :
    tensorWeight p y * (∑ s : ι → Bool,
      tensorBasis p s x * tensorBasis p s y / tensorNorm p s) =
        if x = y then 1 else 0 := by
  rw [tensorBasis_resolution_product, tensorWeight, ← Finset.prod_mul_distrib]
  simp_rw [coordinateBasis_resolution _ (hp0 _) (hp1 _)]
  by_cases h : x = y
  · subst y
    simp
  · simp only [if_neg h]
    have hall : ¬ ∀ i, x i = y i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorBasis_orthogonal
#print axioms Erdos883.SecondSpectral.tensorBasis_resolution
