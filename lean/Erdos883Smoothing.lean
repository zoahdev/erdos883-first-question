import Mathlib.Data.Finset.Card

namespace Erdos883Verified

open Finset

variable {α : Type*} [DecidableEq α]

/-- Finite counting behind retention smoothing. `T` is a set of discarded elements;
if a retained element lies outside the prefix `P`, all of `T` also lies outside it.
The theorem assumes that separation property and does not construct an ordering. -/
theorem retention_smoothing
    (O P Y T : Finset α) (b : ℕ)
    (hYO : Y ⊆ O) (hTO : T ⊆ O) (hYT : Disjoint Y T)
    (hb : b ≤ T.card)
    (hsep : (Y \ P).Nonempty → T ∩ P = ∅) :
    (Y \ P).card ≤ (O \ P).card - b := by
  by_cases hne : (Y \ P).Nonempty
  · have hTP : Disjoint T P := disjoint_iff_inter_eq_empty.mpr (hsep hne)
    have hd : Disjoint (Y \ P) T := by
      apply disjoint_left.mpr
      intro a ha hat
      exact disjoint_left.mp hYT (mem_sdiff.mp ha).1 hat
    have hs : (Y \ P) ∪ T ⊆ O \ P := by
      intro a ha
      rcases mem_union.mp ha with hay | hat
      · exact mem_sdiff.mpr ⟨hYO (mem_sdiff.mp hay).1, (mem_sdiff.mp hay).2⟩
      · exact mem_sdiff.mpr ⟨hTO hat, disjoint_left.mp hTP hat⟩
    have hc := card_le_card hs
    rw [card_union_of_disjoint hd] at hc
    omega
  · have hempty : Y \ P = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Partition accounting: a selected element belongs to exactly one of `E` and `O`.
Every missing element of `E` is balanced by an additional selected element of `O`. -/
theorem selected_odd_card_add_even_card
    (A E O : Finset α)
    (hcover : A ⊆ E ∪ O) (hEO : Disjoint E O) :
    (A ∩ O).card + E.card = A.card + (E \ A).card := by
  have hpartition : A = (A ∩ E) ∪ (A ∩ O) := by
    ext a
    constructor
    · intro ha
      rcases mem_union.mp (hcover ha) with he | ho
      · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨ha, he⟩))
      · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨ha, ho⟩))
    · intro ha
      rcases mem_union.mp ha with he | ho
      · exact (mem_inter.mp he).1
      · exact (mem_inter.mp ho).1
  have hd : Disjoint (A ∩ E) (A ∩ O) := by
    apply disjoint_left.mpr
    intro a he ho
    exact disjoint_left.mp hEO (mem_inter.mp he).2 (mem_inter.mp ho).2
  have hc : A.card = (A ∩ E).card + (A ∩ O).card := by
    conv_lhs => rw [hpartition]
    exact card_union_of_disjoint hd
  have hm := card_sdiff_add_card_inter E A
  rw [inter_comm E A] at hm
  omega

/-- A density threshold produces the odd-element surplus needed before smoothing.
The condition `E.card ≤ f` ensures the natural-number threshold is not truncated. -/
theorem density_gives_odd_surplus
    (A E O : Finset α) (f : ℕ)
    (hcover : A ⊆ E ∪ O) (hEO : Disjoint E O)
    (hEf : E.card ≤ f) (hdense : f < A.card) :
    (f - E.card + 1) + (E \ A).card ≤ (A ∩ O).card := by
  have hc := selected_odd_card_add_even_card A E O hcover hEO
  omega

#print axioms retention_smoothing
#print axioms selected_odd_card_add_even_card
#print axioms density_gives_odd_surplus

end Erdos883Verified
