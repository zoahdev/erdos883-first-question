import Erdos883SecondSpectralFull
import Erdos883SecondSpectralCoupling

/-! The independent triangle density in the full finite signature space.
The product-state reindexing gives the exact small-coordinate contribution
needed by the concrete 48 and 96 coupling bounds. -/

namespace Erdos883.SecondSpectral

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev FullSignatureTriple (ι : Type*) := FullSignature ι × FullSignature ι × FullSignature ι
abbrev FullTripleState (ι : Type*) := TripleBit × TripleBit × (ι → TripleBit)

def fullSignatureDisjoint (x y : FullSignature ι) : Prop :=
  ¬ (x.1 = true ∧ y.1 = true) ∧
  ¬ (x.2.1 = true ∧ y.2.1 = true) ∧
  ∀ i, ¬ (x.2.2 i = true ∧ y.2.2 i = true)

instance : DecidableRel (fullSignatureDisjoint : FullSignature ι → FullSignature ι → Prop) :=
  fun x y => by unfold fullSignatureDisjoint; infer_instance

def fullTriangleAllowed (z : FullSignatureTriple ι) : Prop :=
  fullSignatureDisjoint z.1 z.2.1 ∧ fullSignatureDisjoint z.1 z.2.2 ∧
    fullSignatureDisjoint z.2.1 z.2.2

instance : DecidablePred (fullTriangleAllowed : FullSignatureTriple ι → Prop) :=
  fun z => by unfold fullTriangleAllowed; infer_instance

def fullTriangleDensity (q : ι → ℕ) (f : FullSignature ι → ℝ) : ℝ :=
  ∑ z : FullSignatureTriple ι, if fullTriangleAllowed z then
    (fullSignatureWeight q z.1 * fullSignatureWeight q z.2.1 *
      fullSignatureWeight q z.2.2) * (f z.1 * f z.2.1 * f z.2.2) else 0

def splitFullTriple : FullSignatureTriple ι ≃ FullTripleState ι where
  toFun z := ((z.1.1, z.2.1.1, z.2.2.1),
    (z.1.2.1, z.2.1.2.1, z.2.2.2.1),
      fun i => (z.1.2.2 i, z.2.1.2.2 i, z.2.2.2.2 i))
  invFun z := ((z.1.1, z.2.1.1, fun i => (z.2.2 i).1),
    (z.1.2.1, z.2.1.2.1, fun i => (z.2.2 i).2.1),
    (z.1.2.2, z.2.1.2.2, fun i => (z.2.2 i).2.2))
  left_inv z := by
    rcases z with ⟨⟨a, b, x⟩, ⟨c, d, y⟩, ⟨e, h, z⟩⟩
    rfl
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext rfl (Prod.ext rfl rfl)
    · apply Prod.ext
      · exact Prod.ext rfl (Prod.ext rfl rfl)
      · funext i
        exact Prod.ext rfl (Prod.ext rfl rfl)

def fullTripleProduct (f : FullSignature ι → ℝ) (b2 b3 : TripleBit)
    (z : ι → TripleBit) : ℝ :=
  f (b2.1, b3.1, fun i => (z i).1) *
    f (b2.2.1, b3.2.1, fun i => (z i).2.1) *
    f (b2.2.2, b3.2.2, fun i => (z i).2.2)

omit [Fintype ι] [DecidableEq ι] in
theorem fullTripleProduct_bounds (f : FullSignature ι → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (b2 b3 : TripleBit) (z : ι → TripleBit) :
    0 ≤ fullTripleProduct f b2 b3 z ∧ fullTripleProduct f b2 b3 z ≤ 1 := by
  constructor
  · exact mul_nonneg (mul_nonneg (hf _).1 (hf _).1) (hf _).1
  · exact mul_le_one₀ (mul_le_one₀ (hf _).2 (hf _).1 (hf _).2) (hf _).1 (hf _).2

omit [Fintype ι] [DecidableEq ι] in
theorem splitFullTriple_allowed (z : FullSignatureTriple ι) :
    fullTriangleAllowed z ↔
      tripleBitAllowed (splitFullTriple z).1 ∧
      tripleBitAllowed (splitFullTriple z).2.1 ∧
      tensorTripleAllowed (splitFullTriple z).2.2 := by
  simp only [fullTriangleAllowed, fullSignatureDisjoint, splitFullTriple,
    Equiv.coe_fn_mk, tripleBitAllowed, tensorTripleAllowed]
  constructor
  · rintro ⟨⟨h2xy, h3xy, hpxy⟩, ⟨h2xz, h3xz, hpxz⟩, ⟨h2yz, h3yz, hpyz⟩⟩
    exact ⟨⟨h2xy, h2xz, h2yz⟩, ⟨h3xy, h3xz, h3yz⟩,
      fun i => ⟨hpxy i, hpxz i, hpyz i⟩⟩
  · rintro ⟨⟨h2xy, h2xz, h2yz⟩, ⟨h3xy, h3xz, h3yz⟩, hp⟩
    exact ⟨⟨h2xy, h3xy, fun i => (hp i).1⟩,
      ⟨h2xz, h3xz, fun i => (hp i).2.1⟩,
      ⟨h2yz, h3yz, fun i => (hp i).2.2⟩⟩

 theorem splitFullTriple_weight (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (z : FullSignatureTriple ι) :
    fullSignatureWeight q z.1 * fullSignatureWeight q z.2.1 * fullSignatureWeight q z.2.2 =
      coordinateIndependentTripleWeight 2 (splitFullTriple z).1 *
        coordinateIndependentTripleWeight 3 (splitFullTriple z).2.1 *
        tensorIndependentTripleWeight q (splitFullTriple z).2.2 := by
  rw [coordinateIndependentTripleWeight_tensor 2 (by decide),
    coordinateIndependentTripleWeight_tensor 3 (by decide),
    tensorIndependentTripleWeight_tensor q hq]
  simp only [fullSignatureWeight, splitFullTriple, Equiv.coe_fn_mk]
  ring

 theorem fullTriangleDensity_state (q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (f : FullSignature ι → ℝ) : fullTriangleDensity q f =
      ∑ b2 : TripleBit, ∑ b3 : TripleBit, ∑ z : ι → TripleBit,
        if tripleBitAllowed b2 ∧ tripleBitAllowed b3 ∧ tensorTripleAllowed z then
          (coordinateIndependentTripleWeight 2 b2 * coordinateIndependentTripleWeight 3 b3 *
            tensorIndependentTripleWeight q z) * fullTripleProduct f b2 b3 z else 0 := by
  have heq : fullTriangleDensity q f =
      ∑ z : FullTripleState ι, if tripleBitAllowed z.1 ∧
        tripleBitAllowed z.2.1 ∧ tensorTripleAllowed z.2.2 then
          (coordinateIndependentTripleWeight 2 z.1 * coordinateIndependentTripleWeight 3 z.2.1 *
            tensorIndependentTripleWeight q z.2.2) * fullTripleProduct f z.1 z.2.1 z.2.2 else 0 := by
    unfold fullTriangleDensity
    apply Fintype.sum_equiv splitFullTriple
    intro z
    simp only [splitFullTriple_allowed]
    rw [splitFullTriple_weight q hq]
    rfl
  rw [heq]
  simp only [Fintype.sum_prod_type]

 theorem fullTriangleDensity_fixed_slice (q : ι → ℕ) (hq : ∀ i, 5 ≤ q i)
    (f : FullSignature ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (b2 b3 : TripleBit) (hb2 : tripleBitAllowed b2) (hb3 : tripleBitAllowed b3) :
    (∑ z : ι → TripleBit, if tensorTripleAllowed z then
      (coordinateIndependentTripleWeight 2 b2 * coordinateIndependentTripleWeight 3 b3 *
        tensorIndependentTripleWeight q z) * fullTripleProduct f b2 b3 z else 0) ≤
      fullTriangleDensity q f := by
  have hq0 : ∀ i, q i ≠ 0 := by intro i; have h := hq i; omega
  rw [fullTriangleDensity_state q hq0]
  let term : TripleBit → TripleBit → (ι → TripleBit) → ℝ := fun a b z =>
    if tripleBitAllowed a ∧ tripleBitAllowed b ∧ tensorTripleAllowed z then
      (coordinateIndependentTripleWeight 2 a * coordinateIndependentTripleWeight 3 b *
        tensorIndependentTripleWeight q z) * fullTripleProduct f a b z else 0
  have ht : ∀ a b z, 0 ≤ term a b z := by
    intro a b z
    dsimp [term]
    split_ifs
    · apply mul_nonneg
      · exact mul_nonneg (mul_nonneg
          (by rw [coordinateIndependentTripleWeight_two]; norm_num)
          (le_of_lt (coordinateIndependentTripleWeight_pos 3 (by decide) b)))
          (le_of_lt (tensorIndependentTripleWeight_pos q
            (fun i => Nat.le_trans (by norm_num) (hq i)) z))
      · exact mul_nonneg (mul_nonneg (hf _) (hf _)) (hf _)
    · exact le_rfl
  have h1 : (∑ z : ι → TripleBit, term b2 b3 z) ≤
      ∑ a : TripleBit, ∑ b : TripleBit, ∑ z : ι → TripleBit, term a b z := by
    have hmid : (∑ z : ι → TripleBit, term b2 b3 z) ≤
        ∑ b : TripleBit, ∑ z : ι → TripleBit, term b2 b z :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun z _ => ht b2 b z))
        (Finset.mem_univ b3)
    exact hmid.trans (Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun z _ => ht a b z)))
        (Finset.mem_univ b2))
  simpa [term, hb2, hb3] using h1

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.fullTriangleDensity_fixed_slice

