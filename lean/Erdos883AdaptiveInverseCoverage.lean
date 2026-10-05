import Erdos883AdaptiveCertificateProfiles

namespace Erdos883Verified

/-- A bounded inverse lookup covers all odds, and exact length then forces uniqueness. -/
theorem oddPermutation_of_coverage {L : List ℕ} {U : ℕ}
    (hlen : L.length = coreHalfOdds U)
    (hcover : ∀ i : ℕ, i < coreHalfOdds U → 2*i+1 ∈ L) :
    L.Nodup ∧ L.toFinset = oddUniverse U := by
  have hsub : oddUniverse U ⊆ L.toFinset := by
    intro v hv
    obtain ⟨hvI, hvodd⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv1, hvU⟩ := Finset.mem_Icc.mp hvI
    obtain ⟨i, hi⟩ := hvodd
    have hiU : i < coreHalfOdds U := by unfold coreHalfOdds; omega
    apply List.mem_toFinset.mpr
    convert hcover i hiU using 1 <;> omega
  have hcard : L.toFinset.card = L.length := by
    have hlo := Finset.card_le_card hsub
    rw [oddUniverse_card] at hlo
    change coreHalfOdds U ≤ L.toFinset.card at hlo
    rw [← hlen] at hlo
    exact Nat.le_antisymm (List.toFinset_card_le _) hlo
  have hnd : L.Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (L : Multiset ℕ))).mp hcard
  refine ⟨hnd, (Finset.eq_of_subset_of_card_le hsub ?_).symm⟩
  rw [hcard, hlen, oddUniverse_card]
  exact le_rfl

/-- The same result for the values in a profile table. -/
theorem adaptiveProfilePermutation_of_coverage {rows : List AdaptiveProfileRow} {U : ℕ}
    (hlen : rows.length = halfOdds U)
    (hcover : ∀ i : Fin (halfOdds U), ∃ row ∈ rows, row.value = 2*i.val+1) :
    (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U := by
  apply oddPermutation_of_coverage
  · simpa only [coreProfileValues, List.length_map, halfOdds, coreHalfOdds] using hlen
  · intro i hi
    obtain ⟨row, hrow, heq⟩ := hcover ⟨i, hi⟩
    exact List.mem_map.mpr ⟨row, hrow, heq⟩

/-- Bounded inverse-rank lookups provide the coverage needed above. -/
theorem adaptiveProfilePermutation_of_inverse {rows : List AdaptiveProfileRow} {U : ℕ}
    (hlen : rows.length = halfOdds U)
    (inverse : Fin (halfOdds U) → Fin rows.length)
    (hlookup : ∀ i, (rows[inverse i]).value = 2*i.val+1) :
    (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U := by
  apply adaptiveProfilePermutation_of_coverage hlen
  intro i
  exact ⟨rows[inverse i], List.getElem_mem _, hlookup i⟩

#print axioms oddPermutation_of_coverage
#print axioms adaptiveProfilePermutation_of_coverage
#print axioms adaptiveProfilePermutation_of_inverse
end Erdos883Verified
