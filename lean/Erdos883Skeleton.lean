import Erdos883PrimeSignatures
import Erdos883TransitionGaps
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

namespace Erdos883Verified

/-- Sorting an arbitrary middle block by its full divisibility code, then
 adjoining prescribed endpoints, controls all divisor prefixes at once. -/
theorem divisorSignature_sorted_middle_endpoints_bound
    (ps middle : List ℕ) (a b : ℕ) :
    ∀ s ≤ ps.length, signatureTransitions
      ((a :: (fullSignatureOrder (divisorSignatureCode ps) middle ++ [b])).map
        (divisorSignatureCode (ps.take s))) ≤ 2 ^ s + 1 := by
  intro s hs
  have hsort := divisorSignatureOrder_all_prefix_bounds ps middle s hs
  have hend := signatureTransitions_add_endpoints_le
    ((fullSignatureOrder (divisorSignatureCode ps) middle).map
      (divisorSignatureCode (ps.take s)))
    (divisorSignatureCode (ps.take s) a) (divisorSignatureCode (ps.take s) b)
  have hpow : 0 < 2 ^ s := Nat.pow_pos (by decide)
  simp only [List.map_cons, List.map_append, List.map_nil] at *
  omega

/-- Choose the required number of distinct interior vertices, then sort them
 once. The specified endpoints are retained and every divisor prefix has few
 transitions in this single list. -/
theorem exists_divisor_skeleton_list
    (Y : Finset ℕ) (ps : List ℕ) (a b k : ℕ)
    (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b)
    (hk : 1 ≤ k) (hcard : k + 1 ≤ Y.card) :
    ∃ middle : List ℕ,
      middle.length = k - 1 ∧
      (a :: (middle ++ [b])).Nodup ∧
      (∀ v ∈ a :: (middle ++ [b]), v ∈ Y) ∧
      (∀ s ≤ ps.length, signatureTransitions
        ((a :: (middle ++ [b])).map (divisorSignatureCode (ps.take s))) ≤ 2 ^ s + 1) ∧
      signatureTransitions
        ((a :: (middle ++ [b])).map (divisorSignatureCode (ps.take 0))) = 0 := by
  classical
  have hbe : b ∈ Y.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hsize : k - 1 ≤ ((Y.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨M, hM, hMc⟩ := Finset.exists_subset_card_eq hsize
  let middle := fullSignatureOrder (divisorSignatureCode ps) M.toList
  have hperm : middle.Perm M.toList := fullSignatureOrder_perm _ _
  have hlen : middle.length = k - 1 := by
    rw [hperm.length_eq, Finset.length_toList, hMc]
  have hmiddle : ∀ v ∈ middle, v ∈ Y ∧ v ≠ a ∧ v ≠ b := by
    intro v hv
    have hm := hM (Finset.mem_toList.mp (hperm.mem_iff.mp hv))
    rcases Finset.mem_erase.mp hm with ⟨hvb, hva⟩
    rcases Finset.mem_erase.mp hva with ⟨hva, hvY⟩
    exact ⟨hvY, hva, hvb⟩
  have hma : a ∉ middle := by
    intro h
    exact (hmiddle a h).2.1 rfl
  have hmb : b ∉ middle := by
    intro h
    exact (hmiddle b h).2.2 rfl
  have hnodup : (a :: (middle ++ [b])).Nodup := by
    have hmnd : middle.Nodup := hperm.nodup_iff.mpr M.nodup_toList
    simp only [List.nodup_cons, List.mem_append, List.mem_singleton, not_or]
    refine ⟨⟨hma, hab⟩, ?_⟩
    apply (List.nodup_append).mpr
    refine ⟨hmnd, by simp, ?_⟩
    intro v hv w hw
    have hwb : w = b := by simpa using hw
    subst w
    exact (hmiddle v hv).2.2
  refine ⟨middle, hlen, hnodup, ?_, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact ha
    · exact (hmiddle v hv).1
    · exact hb
  · exact divisorSignature_sorted_middle_endpoints_bound ps M.toList a b
  · exact divisorSignatureCode_zeroPrefix_transitions_eq_zero ps _

/-- The endpoint-preserving skeleton as an injective finite-indexed map.
 One map works for every initial divisor list, and the transition bounds
 count actual adjacent gaps. -/
theorem exists_divisor_skeleton
    (Y : Finset ℕ) (ps : List ℕ) (a b k : ℕ)
    (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b)
    (hk : 1 ≤ k) (hcard : k + 1 ≤ Y.card) :
    ∃ o : Fin (k + 1) → ℕ,
      Function.Injective o ∧
      (∀ i, o i ∈ Y) ∧
      o 0 = a ∧ o (Fin.last k) = b ∧
      (∀ s ≤ ps.length,
        (signatureTransitionGaps (fun i => divisorSignatureCode (ps.take s) (o i))).card
          ≤ 2 ^ s + 1) ∧
      (signatureTransitionGaps (fun i => divisorSignatureCode (ps.take 0) (o i))).card = 0 := by
  obtain ⟨middle, hlen, hnd, hmem, hbound, hzero⟩ :=
    exists_divisor_skeleton_list Y ps a b k ha hb hab hk hcard
  let L := a :: (middle ++ [b])
  have hlength : L.length = k + 1 := by
    simp only [L, List.length_cons, List.length_append, List.length_nil]
    omega
  let o : Fin (k + 1) → ℕ := fun i => L.get (Fin.cast hlength.symm i)
  have ho : List.ofFn o = L :=
    (List.ofFn_congr hlength L.get).symm.trans (List.ofFn_get L)
  refine ⟨o, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hnd.injective_get.comp (Fin.cast_injective hlength.symm)
  · intro i
    exact hmem (o i) (List.get_mem L (Fin.cast hlength.symm i))
  · simp [o, L]
  · have hindex : k < (a :: (middle ++ [b])).length := by
      change k < L.length
      omega
    change (a :: (middle ++ [b]))[k] = b
    have hk' : k = middle.length + 1 := by omega
    simp only [hk', List.getElem_cons_succ]
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp
  · intro s hs
    rw [signatureTransitionGaps_card, List.ofFn_comp', ho]
    exact hbound s hs
  · rw [signatureTransitionGaps_card, List.ofFn_comp', ho]
    exact hzero

#print axioms divisorSignature_sorted_middle_endpoints_bound
#print axioms exists_divisor_skeleton_list
#print axioms exists_divisor_skeleton

end Erdos883Verified
