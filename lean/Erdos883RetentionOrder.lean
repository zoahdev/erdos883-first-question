import Erdos883Smoothing
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Nodup

namespace Erdos883Verified

open Finset

variable {α : Type*} [DecidableEq α]

/-- Selected elements listed in the one fixed ambient order. -/
def selectedInOrder (O : List α) (S : Finset α) : List α :=
  O.filter (fun a => decide (a ∈ S))

/-- Keep the first `M` selected elements in the fixed ambient order. -/
def retainedInOrder (O : List α) (S : Finset α) (M : ℕ) : Finset α :=
  ((selectedInOrder O S).take M).toFinset

/-- Discard all selected elements after the first `M`. -/
def discardedInOrder (O : List α) (S : Finset α) (M : ℕ) : Finset α :=
  ((selectedInOrder O S).drop M).toFinset

/-- A prefix of the single ambient ordering, as a finite set. -/
def orderPrefix (O : List α) (k : ℕ) : Finset α := (O.take k).toFinset

theorem selectedInOrder_nodup (O : List α) (S : Finset α) (hO : O.Nodup) :
    (selectedInOrder O S).Nodup := hO.filter _

@[simp] theorem mem_selectedInOrder (O : List α) (S : Finset α) (a : α) :
    a ∈ selectedInOrder O S ↔ a ∈ O ∧ a ∈ S := by
  simp [selectedInOrder]

theorem selectedInOrder_toFinset (O : List α) (S : Finset α)
    (hSO : S ⊆ O.toFinset) : (selectedInOrder O S).toFinset = S := by
  ext a
  simp only [List.mem_toFinset, mem_selectedInOrder]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hSO h), h⟩⟩

theorem selectedInOrder_length (O : List α) (S : Finset α)
    (hO : O.Nodup) (hSO : S ⊆ O.toFinset) :
    (selectedInOrder O S).length = S.card := by
  rw [← List.toFinset_card_of_nodup (selectedInOrder_nodup O S hO),
    selectedInOrder_toFinset O S hSO]

theorem retainedInOrder_subset_selected (O : List α) (S : Finset α) (M : ℕ) :
    retainedInOrder O S M ⊆ S := by
  intro a ha
  exact (mem_selectedInOrder O S a).mp
    (List.mem_of_mem_take (List.mem_toFinset.mp ha)) |>.2

theorem discardedInOrder_subset_selected (O : List α) (S : Finset α) (M : ℕ) :
    discardedInOrder O S M ⊆ S := by
  intro a ha
  exact (mem_selectedInOrder O S a).mp
    (List.mem_of_mem_drop (List.mem_toFinset.mp ha)) |>.2

theorem retainedInOrder_subset (O : List α) (S : Finset α) (M : ℕ) :
    retainedInOrder O S M ⊆ O.toFinset := by
  intro a ha
  exact List.mem_toFinset.mpr ((mem_selectedInOrder O S a).mp
    (List.mem_of_mem_take (List.mem_toFinset.mp ha))).1

theorem discardedInOrder_subset (O : List α) (S : Finset α) (M : ℕ) :
    discardedInOrder O S M ⊆ O.toFinset := by
  intro a ha
  exact List.mem_toFinset.mpr ((mem_selectedInOrder O S a).mp
    (List.mem_of_mem_drop (List.mem_toFinset.mp ha))).1

theorem retainedInOrder_card (O : List α) (S : Finset α) (M : ℕ)
    (hO : O.Nodup) (hSO : S ⊆ O.toFinset) (hM : M ≤ S.card) :
    (retainedInOrder O S M).card = M := by
  unfold retainedInOrder
  rw [List.toFinset_card_of_nodup
    ((List.take_sublist M _).nodup (selectedInOrder_nodup O S hO)),
    List.length_take, selectedInOrder_length O S hO hSO,
    Nat.min_eq_left hM]

theorem discardedInOrder_card (O : List α) (S : Finset α) (M : ℕ)
    (hO : O.Nodup) (hSO : S ⊆ O.toFinset) :
    (discardedInOrder O S M).card = S.card - M := by
  unfold discardedInOrder
  rw [List.toFinset_card_of_nodup
    ((List.drop_sublist M _).nodup (selectedInOrder_nodup O S hO)),
    List.length_drop, selectedInOrder_length O S hO hSO]

theorem retained_discarded_disjoint (O : List α) (S : Finset α) (M : ℕ)
    (hO : O.Nodup) :
    Disjoint (retainedInOrder O S M) (discardedInOrder O S M) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact (selectedInOrder_nodup O S hO).rel_of_mem_take_of_mem_drop
    (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) rfl

theorem retained_discarded_union (O : List α) (S : Finset α) (M : ℕ)
    (hSO : S ⊆ O.toFinset) :
    retainedInOrder O S M ∪ discardedInOrder O S M = S := by
  unfold retainedInOrder discardedInOrder
  rw [← List.toFinset_append, List.take_append_drop, selectedInOrder_toFinset O S hSO]

/-- Filtering respects the decomposition into any prefix and its complement. -/
theorem selectedInOrder_split (O : List α) (S : Finset α) (k : ℕ) :
    selectedInOrder O S =
      selectedInOrder (O.take k) S ++ selectedInOrder (O.drop k) S := by
  unfold selectedInOrder
  rw [← List.filter_append, List.take_append_drop]

/-- If a retained element falls beyond a prefix, that prefix contained fewer
than `M` selected elements. This uses the same retained set for every prefix. -/
theorem selected_prefix_length_lt (O : List α) (S : Finset α) (M k : ℕ)
    (hne : (retainedInOrder O S M \ orderPrefix O k).Nonempty) :
    (selectedInOrder (O.take k) S).length < M := by
  by_contra h
  have hle : M ≤ (selectedInOrder (O.take k) S).length := by omega
  obtain ⟨a, ha⟩ := hne
  obtain ⟨hay, hnot⟩ := Finset.mem_sdiff.mp ha
  have hat : a ∈ (selectedInOrder O S).take M := List.mem_toFinset.mp hay
  rw [selectedInOrder_split O S k, List.take_append_of_le_length hle] at hat
  have hap : a ∈ O.take k := (mem_selectedInOrder (O.take k) S a).mp
    (List.mem_of_mem_take hat) |>.1
  exact hnot (List.mem_toFinset.mpr hap)

/-- Every discarded element is outside every prefix missing a retained element. -/
theorem retainedInOrder_prefix_separation (O : List α) (S : Finset α) (M k : ℕ)
    (hO : O.Nodup)
    (hne : (retainedInOrder O S M \ orderPrefix O k).Nonempty) :
    discardedInOrder O S M ∩ orderPrefix O k = ∅ := by
  have hlt := selected_prefix_length_lt O S M k hne
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hat, hap⟩ := Finset.mem_inter.mp ha
  have had : a ∈ (selectedInOrder O S).drop M := List.mem_toFinset.mp hat
  rw [selectedInOrder_split O S k, List.drop_append,
    List.drop_eq_nil_of_le (Nat.le_of_lt hlt), List.nil_append] at had
  have haod : a ∈ O.drop k := (mem_selectedInOrder (O.drop k) S a).mp
    (List.mem_of_mem_drop had) |>.1
  exact hO.rel_of_mem_take_of_mem_drop (List.mem_toFinset.mp hap) haod rfl

/-- Order-based retention smoothing: first retain `M` selected elements once,
then the cardinality bound holds simultaneously for every ambient prefix. -/
theorem retention_smoothing_in_order (O : List α) (S : Finset α) (M b : ℕ)
    (hO : O.Nodup) (hSO : S ⊆ O.toFinset) (hMb : M + b ≤ S.card) :
    ∀ k : ℕ,
      (retainedInOrder O S M \ orderPrefix O k).card ≤
        (O.toFinset \ orderPrefix O k).card - b := by
  intro k
  apply retention_smoothing O.toFinset (orderPrefix O k)
    (retainedInOrder O S M) (discardedInOrder O S M) b
    (retainedInOrder_subset O S M) (discardedInOrder_subset O S M)
    (retained_discarded_disjoint O S M hO)
  · rw [discardedInOrder_card O S M hO hSO]
    omega
  · exact retainedInOrder_prefix_separation O S M k hO

/-- The constructive retention package needed downstream: one pair of finite
sets works for all prefixes of the fixed ambient order. -/
theorem exists_ordered_retention (O : List α) (S : Finset α) (M b : ℕ)
    (hO : O.Nodup) (hSO : S ⊆ O.toFinset) (hMb : M + b ≤ S.card) :
    ∃ Y T : Finset α,
      Y.card = M ∧ b ≤ T.card ∧ Y ⊆ S ∧ T ⊆ S ∧
      Y ⊆ O.toFinset ∧ T ⊆ O.toFinset ∧ Disjoint Y T ∧ Y ∪ T = S ∧
      (∀ k : ℕ, (Y \ orderPrefix O k).Nonempty → T ∩ orderPrefix O k = ∅) ∧
      (∀ k : ℕ, (Y \ orderPrefix O k).card ≤
        (O.toFinset \ orderPrefix O k).card - b) := by
  refine ⟨retainedInOrder O S M, discardedInOrder O S M,
    retainedInOrder_card O S M hO hSO (by omega), ?_,
    retainedInOrder_subset_selected O S M, discardedInOrder_subset_selected O S M,
    retainedInOrder_subset O S M, discardedInOrder_subset O S M,
    retained_discarded_disjoint O S M hO, retained_discarded_union O S M hSO,
    (fun k => retainedInOrder_prefix_separation O S M k hO),
    retention_smoothing_in_order O S M b hO hSO hMb⟩
  rw [discardedInOrder_card O S M hO hSO]
  omega

#print axioms selectedInOrder_nodup
#print axioms selectedInOrder_toFinset
#print axioms selectedInOrder_length
#print axioms retainedInOrder_card
#print axioms discardedInOrder_card
#print axioms retained_discarded_disjoint
#print axioms retained_discarded_union
#print axioms selected_prefix_length_lt
#print axioms retainedInOrder_prefix_separation
#print axioms retention_smoothing_in_order
#print axioms exists_ordered_retention

end Erdos883Verified
