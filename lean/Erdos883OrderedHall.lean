import Mathlib.Combinatorics.Hall.Finite

/-!
# An ordered form of Hall's theorem

If, for every `j`, fewer than `j` members of a finite indexed family have fewer
than `j` elements, then the family has a system of distinct representatives.
-/

namespace Erdos883

/-- A finite family has distinct representatives if fewer than `j` of its sets
have cardinality below `j`, for each positive `j` up to the number of indices. -/
theorem ordered_hall {ι α : Type*} [Fintype ι] (D : ι → Finset α)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card ι →
      ((Finset.univ : Finset ι).filter (fun i => (D i).card < j)).card < j) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ D i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' D).mp
  intro s
  by_cases hs : s.Nonempty
  · have hpos : 1 ≤ s.card := hs.card_pos
    have hbound : s.card ≤ Fintype.card ι := Finset.card_le_univ s
    have hbad := h s.card hpos hbound
    have hlarge : ∃ i ∈ s, s.card ≤ (D i).card := by
      by_contra hn
      have hsub : s ⊆ (Finset.univ : Finset ι).filter
          (fun i => (D i).card < s.card) := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_⟩
        exact Nat.lt_of_not_ge (fun hh => hn ⟨i, hi, hh⟩)
      exact (Nat.not_le_of_lt hbad) (Finset.card_le_card hsub)
    obtain ⟨i, hi, hcard⟩ := hlarge
    exact hcard.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem D hi))
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [this]

#print axioms ordered_hall

end Erdos883
