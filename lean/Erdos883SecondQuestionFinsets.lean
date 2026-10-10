import Erdos883SecondQuestion

namespace Erdos883Second

/-- The direct number-theoretic form: a hub and two disjoint finite parts. -/
structure FinsetWitness (A : Finset ℕ) (l : ℕ) where
  apex : ℕ
  left : Finset ℕ
  right : Finset ℕ
  apex_mem : apex ∈ A
  left_subset : left ⊆ A
  right_subset : right ⊆ A
  left_card : left.card = l
  right_card : right.card = l
  apex_not_left : apex ∉ left
  apex_not_right : apex ∉ right
  disjoint : Disjoint left right
  apex_left_coprime : ∀ b ∈ left, Nat.Coprime apex b
  apex_right_coprime : ∀ c ∈ right, Nat.Coprime apex c
  left_right_coprime : ∀ b ∈ left, ∀ c ∈ right, Nat.Coprime b c

/-- Indexing finite sets adds no hypothesis and preserves all graph evidence. -/
noncomputable def FinsetWitness.toWitness {A : Finset ℕ} {l : ℕ}
    (W : FinsetWitness A l) : Witness A l := by
  classical
  let eB : Fin l ≃ W.left :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe W.left).trans W.left_card)).symm
  let eC : Fin l ≃ W.right :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe W.right).trans W.right_card)).symm
  refine {
    apex := W.apex
    left := fun i => (eB i).val
    right := fun i => (eC i).val
    apex_mem := W.apex_mem
    left_mem := fun i => W.left_subset (eB i).property
    right_mem := fun i => W.right_subset (eC i).property
    left_injective := fun i j hij => eB.injective (Subtype.ext hij)
    right_injective := fun i j hij => eC.injective (Subtype.ext hij)
    apex_left_ne := ?_
    apex_right_ne := ?_
    left_right_ne := ?_
    apex_left_coprime := fun i => W.apex_left_coprime _ (eB i).property
    apex_right_coprime := fun i => W.apex_right_coprime _ (eC i).property
    left_right_coprime := fun i j =>
      W.left_right_coprime _ (eB i).property _ (eC j).property }
  · intro i h
    apply W.apex_not_left
    rw [h]
    exact (eB i).property
  · intro i h
    apply W.apex_not_right
    rw [h]
    exact (eC i).property
  · intro i j h
    apply Finset.disjoint_left.mp W.disjoint (eB i).property
    rw [h]
    exact (eC j).property

theorem FinsetWitness.contains {A : Finset ℕ} {l : ℕ}
    (W : FinsetWitness A l) : ContainsTripartite A l :=
  W.toWitness.contains

noncomputable def Witness.toFinsetWitness {A : Finset ℕ} {l : ℕ}
    (W : Witness A l) : FinsetWitness A l := by
  classical
  let B := Finset.univ.image W.left
  let C := Finset.univ.image W.right
  have hB : ∀ b ∈ B, ∃ i, W.left i = b := by
    intro b hb
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
    exact ⟨i, hi⟩
  have hC : ∀ c ∈ C, ∃ i, W.right i = c := by
    intro c hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact ⟨i, hi⟩
  refine {
    apex := W.apex
    left := B
    right := C
    apex_mem := W.apex_mem
    left_subset := ?_
    right_subset := ?_
    left_card := ?_
    right_card := ?_
    apex_not_left := ?_
    apex_not_right := ?_
    disjoint := ?_
    apex_left_coprime := ?_
    apex_right_coprime := ?_
    left_right_coprime := ?_ }
  · intro b hb; obtain ⟨i, rfl⟩ := hB b hb; exact W.left_mem i
  · intro c hc; obtain ⟨i, rfl⟩ := hC c hc; exact W.right_mem i
  · simpa [B] using Finset.card_image_of_injective Finset.univ W.left_injective
  · simpa [C] using Finset.card_image_of_injective Finset.univ W.right_injective
  · intro ha; obtain ⟨i, hi⟩ := hB _ ha; exact W.apex_left_ne i hi.symm
  · intro ha; obtain ⟨i, hi⟩ := hC _ ha; exact W.apex_right_ne i hi.symm
  · apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨i, hi⟩ := hB b hb
    obtain ⟨j, hj⟩ := hC b hc
    exact W.left_right_ne i j (hi.trans hj.symm)
  · intro b hb; obtain ⟨i, rfl⟩ := hB b hb; exact W.apex_left_coprime i
  · intro c hc; obtain ⟨i, rfl⟩ := hC c hc; exact W.apex_right_coprime i
  · intro b hb c hc
    obtain ⟨i, rfl⟩ := hB b hb
    obtain ⟨j, rfl⟩ := hC c hc
    exact W.left_right_coprime i j

theorem contains_iff_finsetWitness {A : Finset ℕ} {l : ℕ} :
    ContainsTripartite A l ↔ Nonempty (FinsetWitness A l) :=
  ⟨fun h => ⟨(witnessOfContains h).toFinsetWitness⟩,
    fun ⟨W⟩ => W.contains⟩

#print axioms contains_iff_finsetWitness

end Erdos883Second
