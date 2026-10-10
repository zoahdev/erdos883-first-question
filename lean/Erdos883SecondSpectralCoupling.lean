import Erdos883SecondSpectralTriple

namespace Erdos883.SecondSpectral

noncomputable section
open Erdos883Second.Far

def tripleBitAllowed (b : TripleBit) : Prop :=
  ¬ (b.1 = true ∧ b.2.1 = true) ∧
  ¬ (b.1 = true ∧ b.2.2 = true) ∧
  ¬ (b.2.1 = true ∧ b.2.2 = true)

instance : DecidablePred tripleBitAllowed := fun b => by
  unfold tripleBitAllowed
  infer_instance

 theorem coordinateTripleWeight_support (q : ℕ) (b : TripleBit)
    (hb : ¬ tripleBitAllowed b) : coordinateTripleWeight q b = 0 := by
  rcases b with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp_all [tripleBitAllowed, coordinateTripleWeight, disjointTripleMass]

 theorem coordinateIndependentTripleWeight_two (b : TripleBit) :
    coordinateIndependentTripleWeight 2 b = 1 / 8 := by
  rcases b with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [coordinateIndependentTripleWeight, tripleProductMass, bernoulliMass]

 theorem coordinateIndependentTripleWeight_three_lower (b : TripleBit)
    (hb : tripleBitAllowed b) :
    (4 / 27 : ℝ) ≤ coordinateIndependentTripleWeight 3 b := by
  rcases b with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp_all [tripleBitAllowed, coordinateIndependentTripleWeight,
      tripleProductMass, bernoulliMass] <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorTripleAllowed (z : ι → TripleBit) : Prop := ∀ i, tripleBitAllowed (z i)

instance : DecidablePred (tensorTripleAllowed : (ι → TripleBit) → Prop) := fun z => by
  unfold tensorTripleAllowed
  infer_instance

omit [DecidableEq ι] in
theorem tensorTripleWeight_support (q : ι → ℕ) (z : ι → TripleBit)
    (hz : ¬ tensorTripleAllowed z) : tensorTripleWeight q z = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hz
  exact Finset.prod_eq_zero (Finset.mem_univ i) (coordinateTripleWeight_support _ _ hi)

 theorem tensorTripleL2_large_bound (n : ℕ) (q : ι → ℕ) (hqi : Function.Injective q)
    (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i) (hqn : ∀ i, q i ≤ n) :
    (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      tensorIndependentTripleWeight q z) ≤ 128 := by
  rw [tensorTripleL2_product]
  have hP : ∀ p ∈ Finset.univ.image q, p.Prime ∧ 5 ≤ p := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hq i
  have hn : ∀ p ∈ Finset.univ.image q, p ≤ n := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hqn i
  have h := tripleL2Square_product_bound n (Finset.univ.image q) hP hn
  rw [Finset.prod_image hqi.injOn] at h
  norm_num at h
  simp only [one_div]
  exact_mod_cast h

/-- Fixed odd, odd, even parity costs an independent probability 1/8.
The hypothesis hD places this explicit contribution inside the full
independent-signature triangle density. -/
 theorem tensorTriple_odd_odd_even_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 3 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (g : (ι → TripleBit) → ℝ)
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ 1) (D : ℝ)
    (hD : (∑ z : ι → TripleBit, if tensorTripleAllowed z then
      (tensorIndependentTripleWeight q z / 8) * g z else 0) ≤ D) :
    (∑ z : ι → TripleBit, tensorTripleWeight q z * g z) ≤ 48 * Real.sqrt D := by
  classical
  have hw : ∀ z, 0 < tensorIndependentTripleWeight q z / 8 := by
    intro z
    exact div_pos (tensorIndependentTripleWeight_pos q (fun i => (hq i).2) z) (by norm_num)
  have hL2 : (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      (tensorIndependentTripleWeight q z / 8)) ≤ (48 : ℝ)^2 := by
    have h := tensorTripleL2_bound n q hqi hq hqn
    have heq : (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      (tensorIndependentTripleWeight q z / 8)) =
        8 * (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
          tensorIndependentTripleWeight q z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [heq]
    nlinarith [h]
  exact coupling_expectation_bound (fun z => tensorIndependentTripleWeight q z / 8)
    (tensorTripleWeight q) g tensorTripleAllowed 48 D hw (fun z => (hg z).1)
      (fun z => (hg z).2) (tensorTripleWeight_support q) (by norm_num) hL2 hD

/-- Any disjoint fixed pattern at 2 and 3 costs probability at least 1/54.
The large-prime product norm is at most 128; hence the total square norm
is at most 6912, and the clean coefficient 96 applies. -/
 theorem tensorTriple_fixed_two_three_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (b2 b3 : TripleBit)
    (hb3 : tripleBitAllowed b3) (g : (ι → TripleBit) → ℝ)
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ 1) (D : ℝ)
    (hD : (∑ z : ι → TripleBit, if tensorTripleAllowed z then
      (coordinateIndependentTripleWeight 2 b2 * coordinateIndependentTripleWeight 3 b3 *
        tensorIndependentTripleWeight q z) * g z else 0) ≤ D) :
    (∑ z : ι → TripleBit, tensorTripleWeight q z * g z) ≤ 96 * Real.sqrt D := by
  classical
  let c : ℝ := coordinateIndependentTripleWeight 2 b2 * coordinateIndependentTripleWeight 3 b3
  have hc : (1 / 54 : ℝ) ≤ c := by
    dsimp [c]
    rw [coordinateIndependentTripleWeight_two]
    have h := coordinateIndependentTripleWeight_three_lower b3 hb3
    linarith
  have hc0 : 0 < c := by linarith
  have hw : ∀ z, 0 < c * tensorIndependentTripleWeight q z := by
    intro z
    exact mul_pos hc0 (tensorIndependentTripleWeight_pos q
      (fun i => Nat.le_trans (by norm_num) (hq i).2) z)
  have hL2 : (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      (c * tensorIndependentTripleWeight q z)) ≤ (96 : ℝ)^2 := by
    have h := tensorTripleL2_large_bound n q hqi hq hqn
    have heq : (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
      (c * tensorIndependentTripleWeight q z)) =
        (∑ z : ι → TripleBit, (tensorTripleWeight q z)^2 /
          tensorIndependentTripleWeight q z) / c := by
      simp only [div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [heq]
    apply (div_le_iff₀ hc0).mpr
    nlinarith [h]
  exact coupling_expectation_bound (fun z => c * tensorIndependentTripleWeight q z)
    (tensorTripleWeight q) g tensorTripleAllowed 96 D hw (fun z => (hg z).1)
      (fun z => (hg z).2) (tensorTripleWeight_support q) (by norm_num) hL2 hD

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorTriple_odd_odd_even_bound
#print axioms Erdos883.SecondSpectral.tensorTriple_fixed_two_three_bound

