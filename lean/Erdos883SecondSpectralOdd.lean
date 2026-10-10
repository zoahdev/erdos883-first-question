import Erdos883SecondSpectralDensity

namespace Erdos883.SecondSpectral

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def splitOddTriple : (Option ι → TripleBit) ≃ TripleBit × (ι → TripleBit) where
  toFun x := (x none, fun i => x (some i))
  invFun x := fun i => match i with | none => x.1 | some j => x.2 j
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by rcases x with ⟨b, y⟩; rfl

omit [Fintype ι] [DecidableEq ι] in
theorem tensorTripleAllowed_withThree (z : Option ι → TripleBit) :
    tensorTripleAllowed z ↔ tripleBitAllowed (z none) ∧
      tensorTripleAllowed (fun i => z (some i)) := by
  constructor
  · intro h
    exact ⟨h none, fun i => h (some i)⟩
  · rintro ⟨h0, h⟩ i
    cases i with
    | none => exact h0
    | some i => exact h i

omit [DecidableEq ι] in
theorem tensorIndependentTripleWeight_withThree (q : ι → ℕ) (z : Option ι → TripleBit) :
    tensorIndependentTripleWeight (oddPrimeLabels q) z =
      coordinateIndependentTripleWeight 3 (z none) *
        tensorIndependentTripleWeight q (fun i => z (some i)) := by
  simp only [tensorIndependentTripleWeight, Fintype.prod_option, oddPrimeLabels]

 def oddOddEvenProduct (f : FullSignature ι → ℝ) (z : Option ι → TripleBit) : ℝ :=
  fullParityFunction f false (fun i => (z i).1) *
    fullParityFunction f false (fun i => (z i).2.1) *
    fullParityFunction f true (fun i => (z i).2.2)

omit [Fintype ι] [DecidableEq ι] in
theorem oddOddEvenProduct_bounds (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (z : Option ι → TripleBit) :
    0 ≤ oddOddEvenProduct f z ∧ oddOddEvenProduct f z ≤ 1 := by
  constructor
  · exact mul_nonneg (mul_nonneg (hf _).1 (hf _).1) (hf _).1
  · exact mul_le_one₀ (mul_le_one₀ (hf _).2 (hf _).1 (hf _).2) (hf _).1 (hf _).2

 theorem fullTriangleDensity_odd_odd_even_slice (q : ι → ℕ) (hq : ∀ i, 5 ≤ q i)
    (f : FullSignature ι → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ z : Option ι → TripleBit, if tensorTripleAllowed z then
      (tensorIndependentTripleWeight (oddPrimeLabels q) z / 8) * oddOddEvenProduct f z
        else 0) ≤ fullTriangleDensity q f := by
  have hq0 : ∀ i, q i ≠ 0 := by intro i; have h := hq i; omega
  have heq : (∑ z : Option ι → TripleBit, if tensorTripleAllowed z then
      (tensorIndependentTripleWeight (oddPrimeLabels q) z / 8) * oddOddEvenProduct f z
        else 0) =
      ∑ b3 : TripleBit, ∑ z : ι → TripleBit,
        if tripleBitAllowed b3 ∧ tensorTripleAllowed z then
          (coordinateIndependentTripleWeight 2 (false, false, true) *
            coordinateIndependentTripleWeight 3 b3 * tensorIndependentTripleWeight q z) *
              fullTripleProduct f (false, false, true) b3 z else 0 := by
    have heq' : (∑ z : Option ι → TripleBit, if tensorTripleAllowed z then
      (tensorIndependentTripleWeight (oddPrimeLabels q) z / 8) * oddOddEvenProduct f z
        else 0) =
      ∑ z : TripleBit × (ι → TripleBit),
        if tripleBitAllowed z.1 ∧ tensorTripleAllowed z.2 then
          (coordinateIndependentTripleWeight 2 (false, false, true) *
            coordinateIndependentTripleWeight 3 z.1 * tensorIndependentTripleWeight q z.2) *
              fullTripleProduct f (false, false, true) z.1 z.2 else 0 := by
      apply Fintype.sum_equiv splitOddTriple
      intro z
      have hiff : tensorTripleAllowed z ↔
          tripleBitAllowed (splitOddTriple z).1 ∧ tensorTripleAllowed (splitOddTriple z).2 :=
        tensorTripleAllowed_withThree z
      by_cases ha : tensorTripleAllowed z
      · rw [if_pos ha, if_pos (hiff.mp ha)]
        rw [tensorIndependentTripleWeight_withThree, coordinateIndependentTripleWeight_two]
        dsimp [oddOddEvenProduct, fullParityFunction, fullTripleProduct, splitOddTriple]
        ring
      · rw [if_neg ha, if_neg (fun hr => ha (hiff.mpr hr))]
    rw [heq', Fintype.sum_prod_type]
  rw [heq, fullTriangleDensity_state q hq0]
  let term : TripleBit → TripleBit → (ι → TripleBit) → ℝ := fun b2 b3 z =>
    if tripleBitAllowed b2 ∧ tripleBitAllowed b3 ∧ tensorTripleAllowed z then
      (coordinateIndependentTripleWeight 2 b2 * coordinateIndependentTripleWeight 3 b3 *
        tensorIndependentTripleWeight q z) * fullTripleProduct f b2 b3 z else 0
  have ht : ∀ b2 b3 z, 0 ≤ term b2 b3 z := by
    intro b2 b3 z
    dsimp [term]
    split_ifs
    · apply mul_nonneg
      · exact mul_nonneg (mul_nonneg
          (by rw [coordinateIndependentTripleWeight_two]; norm_num)
          (le_of_lt (coordinateIndependentTripleWeight_pos 3 (by decide) b3)))
          (le_of_lt (tensorIndependentTripleWeight_pos q
            (fun i => Nat.le_trans (by norm_num) (hq i)) z))
      · exact mul_nonneg (mul_nonneg (hf _) (hf _)) (hf _)
    · exact le_rfl
  have h : (∑ b3 : TripleBit, ∑ z : ι → TripleBit, term (false, false, true) b3 z) ≤
      ∑ b2 : TripleBit, ∑ b3 : TripleBit, ∑ z : ι → TripleBit, term b2 b3 z :=
    Finset.single_le_sum
    (fun b2 (_ : b2 ∈ (Finset.univ : Finset TripleBit)) =>
      Finset.sum_nonneg (fun b3 _ => Finset.sum_nonneg (fun z _ => ht b2 b3 z)))
    (Finset.mem_univ (false, false, true))
  have hb2 : tripleBitAllowed (false, false, true) := by decide
  simpa only [term, hb2, true_and] using h

 theorem fullTriangle_odd_odd_even_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∑ z : Option ι → TripleBit, tensorTripleWeight (oddPrimeLabels q) z *
      oddOddEvenProduct f z) ≤ 48 * Real.sqrt (fullTriangleDensity q f) := by
  apply tensorTriple_odd_odd_even_bound (max n 3) (oddPrimeLabels q)
    (oddPrimeLabels_injective q hqi (fun i => (hq i).2)) (oddPrimeLabels_prime q hq)
    (fun i => by cases i with
      | none => exact le_max_right n 3
      | some i => exact (hqn i).trans (le_max_left n 3))
    (oddOddEvenProduct f) (oddOddEvenProduct_bounds f hf)
  exact fullTriangleDensity_odd_odd_even_slice q (fun i => (hq i).2) f (fun x => (hf x).1)

 theorem fullOddPairCorrelation_bound (n : ℕ) (q : ι → ℕ)
    (hqi : Function.Injective q) (hq : ∀ i, (q i).Prime ∧ 5 ≤ q i)
    (hqn : ∀ i, q i ≤ n) (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    fullOddPairCorrelation q f ≤ 1 - fullParityMean q f true +
      48 * Real.sqrt (fullTriangleDensity q f) := by
  let qo : Option ι → ℕ := oddPrimeLabels q
  have hqo : ∀ i, 3 ≤ qo i := fun i => (oddPrimeLabels_prime q hq i).2
  have hqo0 : ∀ i, qo i ≠ 0 := by intro i; have h := hqo i; omega
  have hpoint : (∑ z : Option ι → TripleBit, tensorTripleWeight qo z *
      fullParityFunction f false (fun i => (z i).1) *
      fullParityFunction f false (fun i => (z i).2.1)) ≤
      (∑ z : Option ι → TripleBit, tensorTripleWeight qo z *
        (1 - fullParityFunction f true (fun i => (z i).2.2))) +
        ∑ z : Option ι → TripleBit, tensorTripleWeight qo z * oddOddEvenProduct f z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    have hm := tensorTripleWeight_nonneg qo hqo z
    have ha : 0 ≤ fullParityFunction f false (fun i => (z i).1) ∧
        fullParityFunction f false (fun i => (z i).1) ≤ 1 := hf _
    have hb : 0 ≤ fullParityFunction f false (fun i => (z i).2.1) ∧
        fullParityFunction f false (fun i => (z i).2.1) ≤ 1 := hf _
    have hc : fullParityFunction f true (fun i => (z i).2.2) ≤ 1 := (hf _).2
    have hab : fullParityFunction f false (fun i => (z i).1) *
        fullParityFunction f false (fun i => (z i).2.1) ≤ 1 :=
      mul_le_one₀ ha.2 hb.1 hb.2
    have hbase := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc)
    have hscaled := mul_nonneg hm hbase
    dsimp [oddOddEvenProduct]
    nlinarith [hscaled]
  rw [tensorTripleWeight_pair_expectation qo hqo0] at hpoint
  have hdef : (∑ z : Option ι → TripleBit, tensorTripleWeight qo z *
        (1 - fullParityFunction f true (fun i => (z i).2.2))) =
      1 - fullParityMean q f true := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [tensorTripleWeight_sum, tensorTripleWeight_third_expectation qo hqo0]
    rw [fullParityMean_tensorMean]
  rw [hdef] at hpoint
  have htriangle := fullTriangle_odd_odd_even_bound n q hqi hq hqn f hf
  change fullOddPairCorrelation q f ≤ _ at hpoint
  linarith [hpoint, htriangle]

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.fullTriangle_odd_odd_even_bound
#print axioms Erdos883.SecondSpectral.fullOddPairCorrelation_bound

