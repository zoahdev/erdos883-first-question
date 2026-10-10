import Erdos883SecondSpectralConditional
import Erdos883SecondCouplingNorm
import Erdos883SecondCouplingEstimate

/-! A concrete finite disjoint three-signature coupling. Its first two
marginals are exactly the correlation kernel used in spectral stability. -/

namespace Erdos883.SecondSpectral

noncomputable section

open Erdos883Second.Far

abbrev TripleBit := Bool × Bool × Bool

def coordinateTripleWeight (q : ℕ) (z : TripleBit) : ℝ :=
  (disjointTripleMass (1 / (q : ℚ)) z : ℝ)

def coordinateIndependentTripleWeight (q : ℕ) (z : TripleBit) : ℝ :=
  (tripleProductMass (1 / (q : ℚ)) z : ℝ)

 theorem coordinateTripleWeight_sum (q : ℕ) :
    (∑ z : TripleBit, coordinateTripleWeight q z) = 1 := by
  have h := disjointTripleMass_sum (1 / (q : ℚ))
  dsimp [coordinateTripleWeight]
  exact_mod_cast h

 theorem coordinateTripleWeight_nonneg (q : ℕ) (hq : 3 ≤ q) (z : TripleBit) :
    0 ≤ coordinateTripleWeight q z := by
  have hqQ : (3 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hqsmall : (1 : ℚ) / q ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) hqQ
  simp only [one_div] at hqsmall
  have h : 0 ≤ disjointTripleMass (1 / (q : ℚ)) z := by
    rcases z with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> simp [disjointTripleMass]
    · linarith
  dsimp [coordinateTripleWeight]
  exact_mod_cast h

 theorem bernoulliMass_coordinateWeight (q : ℕ) (hq : q ≠ 0) (b : Bool) :
    (bernoulliMass (1 / (q : ℚ)) b : ℝ) = coordinateWeight (q : ℝ) b := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  cases b <;> simp [bernoulliMass, coordinateWeight]
  field_simp

 theorem coordinateTripleWeight_pair (q : ℕ) (hq : q ≠ 0) (a b : Bool) :
    (∑ c : Bool, coordinateTripleWeight q (a, b, c)) =
      coordinatePairWeight (q : ℝ) a b := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  cases a <;> cases b <;>
    simp [coordinateTripleWeight, disjointTripleMass, coordinatePairWeight]
  field_simp
  ring

 theorem coordinateTripleWeight_third (q : ℕ) (hq : q ≠ 0) (c : Bool) :
    (∑ ab : Bool × Bool, coordinateTripleWeight q (ab.1, ab.2, c)) =
      coordinateWeight (q : ℝ) c := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  cases c <;>
    simp [Fintype.sum_prod_type, coordinateTripleWeight,
      disjointTripleMass, coordinateWeight]
  field_simp
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorTripleWeight (q : ι → ℕ) (z : ι → TripleBit) : ℝ :=
  ∏ i, coordinateTripleWeight (q i) (z i)

def tensorIndependentTripleWeight (q : ι → ℕ) (z : ι → TripleBit) : ℝ :=
  ∏ i, coordinateIndependentTripleWeight (q i) (z i)

def splitTripleBits : (ι → TripleBit) ≃ (ι → Bool × Bool) × (ι → Bool) where
  toFun z := (fun i => ((z i).1, (z i).2.1), fun i => (z i).2.2)
  invFun z := fun i => ((z.1 i).1, (z.1 i).2, z.2 i)
  left_inv z := by funext i; exact Prod.ext rfl (Prod.ext rfl rfl)
  right_inv z := by rcases z with ⟨z, t⟩; rfl

omit [DecidableEq ι] in
theorem tensorTripleWeight_nonneg (q : ι → ℕ) (hq : ∀ i, 3 ≤ q i)
    (z : ι → TripleBit) : 0 ≤ tensorTripleWeight q z := by
  exact Finset.prod_nonneg (fun i _ => coordinateTripleWeight_nonneg (q i) (hq i) (z i))

 theorem tensorTripleWeight_sum (q : ι → ℕ) :
    (∑ z : ι → TripleBit, tensorTripleWeight q z) = 1 := by
  simp only [tensorTripleWeight]
  rw [← Fintype.prod_sum]
  simp_rw [coordinateTripleWeight_sum]
  simp

 theorem tensorTripleWeight_pair_marginal (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (z : ι → Bool × Bool) :
    (∑ t : ι → Bool, tensorTripleWeight q (fun i => ((z i).1, (z i).2, t i))) =
      tensorPairWeight (fun i => (q i : ℝ)) z := by
  simp only [tensorTripleWeight]
  rw [← Fintype.prod_sum (fun i (b : Bool) => coordinateTripleWeight (q i)
    ((z i).1, (z i).2, b))]
  simp_rw [coordinateTripleWeight_pair _ (hq _)]
  rfl

 theorem tensorTripleWeight_third_marginal (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (t : ι → Bool) :
    (∑ z : ι → Bool × Bool, tensorTripleWeight q (fun i => ((z i).1, (z i).2, t i))) =
      tensorWeight (fun i => (q i : ℝ)) t := by
  simp only [tensorTripleWeight]
  rw [← Fintype.prod_sum (fun i (b : Bool × Bool) => coordinateTripleWeight (q i)
    (b.1, b.2, t i))]
  simp_rw [coordinateTripleWeight_third _ (hq _)]
  rfl

 theorem tensorTripleWeight_pair_expectation (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (f g : (ι → Bool) → ℝ) :
    (∑ z : ι → TripleBit, tensorTripleWeight q z *
      f (fun i => (z i).1) * g (fun i => (z i).2.1)) =
      tensorPairCorrelation (fun i => (q i : ℝ)) f g := by
  calc
    _ = ∑ z : (ι → Bool × Bool) × (ι → Bool),
      tensorTripleWeight q (fun i => ((z.1 i).1, (z.1 i).2, z.2 i)) *
        f (fun i => (z.1 i).1) * g (fun i => (z.1 i).2) := by
          apply Fintype.sum_equiv splitTripleBits
          intro z
          rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_mul, tensorTripleWeight_pair_marginal q hq]
      rfl

 theorem tensorTripleWeight_third_expectation (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (f : (ι → Bool) → ℝ) :
    (∑ z : ι → TripleBit, tensorTripleWeight q z * f (fun i => (z i).2.2)) =
      tensorMean (fun i => (q i : ℝ)) f := by
  calc
    _ = ∑ z : (ι → Bool × Bool) × (ι → Bool),
      tensorTripleWeight q (fun i => ((z.1 i).1, (z.1 i).2, z.2 i)) * f z.2 := by
          apply Fintype.sum_equiv splitTripleBits
          intro z
          rfl
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [← Finset.sum_mul, tensorTripleWeight_third_marginal q hq]
      rfl

 theorem coordinateIndependentTripleWeight_tensor (q : ℕ) (hq : q ≠ 0) (z : TripleBit) :
    coordinateIndependentTripleWeight q z =
      coordinateWeight (q : ℝ) z.1 * coordinateWeight (q : ℝ) z.2.1 *
        coordinateWeight (q : ℝ) z.2.2 := by
  simp only [coordinateIndependentTripleWeight, tripleProductMass, Rat.cast_mul,
    bernoulliMass_coordinateWeight q hq]

omit [DecidableEq ι] in
theorem tensorIndependentTripleWeight_tensor (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (z : ι → TripleBit) :
    tensorIndependentTripleWeight q z =
      tensorWeight (fun i => (q i : ℝ)) (fun i => (z i).1) *
      tensorWeight (fun i => (q i : ℝ)) (fun i => (z i).2.1) *
      tensorWeight (fun i => (q i : ℝ)) (fun i => (z i).2.2) := by
  simp only [tensorIndependentTripleWeight,
    coordinateIndependentTripleWeight_tensor _ (hq _), tensorWeight,
    Finset.prod_mul_distrib]

 theorem coordinateIndependentTripleWeight_pos (q : ℕ) (hq : 3 ≤ q) (z : TripleBit) :
    0 < coordinateIndependentTripleWeight q z := by
  have hq0 : q ≠ 0 := by omega
  rw [coordinateIndependentTripleWeight_tensor q hq0]
  have hw : ∀ b : Bool, 0 < coordinateWeight (q : ℝ) b := by
    intro b
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    cases b <;> simp only [coordinateWeight]
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos (by norm_num) (by linarith)
  exact mul_pos (mul_pos (hw _) (hw _)) (hw _)

omit [DecidableEq ι] in
theorem tensorIndependentTripleWeight_pos (q : ι → ℕ) (hq : ∀ i, 3 ≤ q i)
    (z : ι → TripleBit) : 0 < tensorIndependentTripleWeight q z := by
  exact Finset.prod_pos (fun i _ => coordinateIndependentTripleWeight_pos _ (hq i) (z i))

 theorem coordinateTripleL2_cast (q : ℕ) :
    (∑ z : TripleBit, (coordinateTripleWeight q z)^2 /
      coordinateIndependentTripleWeight q z) =
        (tripleL2Square (1 / (q : ℚ)) : ℝ) := by
  simp only [coordinateTripleWeight, coordinateIndependentTripleWeight,
    tripleL2Square, Rat.cast_sum, Rat.cast_div, Rat.cast_pow]

set_option maxHeartbeats 1000000 in
 theorem tensorTripleL2_product (q : ι → ℕ) :
    (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      tensorIndependentTripleWeight q z) =
        ∏ i, (tripleL2Square (1 / (q i : ℚ)) : ℝ) := by
  calc
    _ = ∑ z : ι → TripleBit, ∏ i,
      (coordinateTripleWeight (q i) (z i))^2 /
        coordinateIndependentTripleWeight (q i) (z i) := by
          simp only [tensorTripleWeight, tensorIndependentTripleWeight,
            Finset.prod_pow, Finset.prod_div_distrib]
    _ = ∏ i, ∑ z : TripleBit, (coordinateTripleWeight (q i) z)^2 /
        coordinateIndependentTripleWeight (q i) z :=
          (Fintype.prod_sum (fun i (z : TripleBit) =>
            (coordinateTripleWeight (q i) z)^2 /
              coordinateIndependentTripleWeight (q i) z)).symm
    _ = _ := by simp_rw [coordinateTripleL2_cast]

 theorem tripleL2Square_odd_product_bound (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) (hn : ∀ p ∈ P, p ≤ n) :
    (∏ p ∈ P, tripleL2Square (1 / (p : ℚ))) ≤ 288 := by
  have h3 : (∏ p ∈ P.filter (fun p => p = 3), tripleL2Square (1 / (p : ℚ))) ≤
      (9 / 4 : ℚ) := by
    rw [Finset.filter_eq']
    split_ifs <;>
      norm_num [tripleL2Square, Fintype.sum_prod_type,
        disjointTripleMass, tripleProductMass, bernoulliMass]
  have hrest : (∏ p ∈ P.filter (fun p => p ≠ 3), tripleL2Square (1 / (p : ℚ))) ≤
      (2 : ℚ)^7 := by
    apply tripleL2Square_product_bound n _
    · intro p hp
      obtain ⟨hpP, hp3⟩ := Finset.mem_filter.mp hp
      have hpprime := (hP p hpP).1
      have hplower := (hP p hpP).2
      exact ⟨hpprime, hpprime.five_le_of_ne_two_of_ne_three (by omega) hp3⟩
    · intro p hp; exact hn p (Finset.mem_filter.mp hp).1
  have hrest0 : 0 ≤ ∏ p ∈ P.filter (fun p => p ≠ 3), tripleL2Square (1 / (p : ℚ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hplower := (hP p (Finset.mem_filter.mp hp).1).2
    have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hplower
    apply tripleL2Square_nonneg (by positivity)
    apply (div_le_iff₀ (by linarith : (0 : ℚ) < p)).mpr
    linarith
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p = 3)]
  have h := mul_le_mul h3 hrest hrest0 (by norm_num : (0 : ℚ) ≤ 9 / 4)
  norm_num at h ⊢
  exact h

 theorem tensorTripleL2_bound (n : ℕ) (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, (q i).Prime ∧ 3 ≤ q i) (hqn : ∀ i, q i ≤ n) :
    (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      tensorIndependentTripleWeight q z) ≤ 288 := by
  rw [tensorTripleL2_product]
  have hP : ∀ p ∈ Finset.univ.image q, p.Prime ∧ 3 ≤ p := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hq i
  have hn : ∀ p ∈ Finset.univ.image q, p ≤ n := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hqn i
  have h := tripleL2Square_odd_product_bound n (Finset.univ.image q) hP hn
  rw [Finset.prod_image hqi.injOn] at h
  exact_mod_cast h

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorTripleWeight_pair_expectation
#print axioms Erdos883.SecondSpectral.tensorTripleWeight_third_expectation
#print axioms Erdos883.SecondSpectral.tensorTripleL2_product
#print axioms Erdos883.SecondSpectral.tensorTripleL2_bound

