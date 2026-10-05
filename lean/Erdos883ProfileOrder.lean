import Erdos883RetentionOrder
import Mathlib.Data.List.Sort

namespace Erdos883Verified

variable {α β : Type*} [LinearOrder β]

/-- Sort once by decreasing profile. The threshold does not enter this ordering. -/
def descendingProfileOrder (f : α → β) (O : List α) : List α :=
  O.mergeSort (fun u v => decide (f v ≤ f u))

/-- Sorting retains every vertex occurrence, including tied profiles. -/
theorem descendingProfileOrder_perm (f : α → β) (O : List α) :
    (descendingProfileOrder f O).Perm O := by
  exact List.mergeSort_perm O _

/-- The constructed order is decreasing in the profile. -/
theorem descendingProfileOrder_pairwise (f : α → β) (O : List α) :
    (descendingProfileOrder f O).Pairwise (fun u v => f v ≤ f u) := by
  unfold descendingProfileOrder
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun u v => decide (f v ≤ f u))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      exact le_trans hbc hab)
    (by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (f b) (f a)) O

theorem descendingProfileOrder_nodup (f : α → β) (O : List α)
    (hO : O.Nodup) : (descendingProfileOrder f O).Nodup :=
  (descendingProfileOrder_perm f O).nodup_iff.mpr hO

@[simp] theorem descendingProfileOrder_length (f : α → β) (O : List α) :
    (descendingProfileOrder f O).length = O.length :=
  (descendingProfileOrder_perm f O).length_eq

/-- Every upper profile level set is an initial segment of a decreasing list.
This is proved from pairwise order, without an assumed prefix property. -/
theorem profile_filter_eq_take (f : α → β) (O : List α) (z : β)
    (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    O.filter (fun v => decide (z ≤ f v)) =
      O.take (O.filter (fun v => decide (z ≤ f v))).length := by
  induction O with
  | nil => simp
  | cons a O ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    by_cases ha : z ≤ f a
    · simpa [ha] using congrArg (List.cons a) (ih htail)
    · have hempty : O.filter (fun v => decide (z ≤ f v)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro v hv hgood
        exact ha (le_trans (of_decide_eq_true hgood) (hhead v hv))
      simp [ha, hempty]

/-- The exact initial segment has precisely the vertices of profile at least `z`. -/
theorem mem_profile_take_iff (f : α → β) (O : List α) (z : β)
    (hsorted : O.Pairwise (fun u v => f v ≤ f u)) (v : α) :
    v ∈ O.take (O.filter (fun w => decide (z ≤ f w))).length ↔
      v ∈ O ∧ z ≤ f v := by
  rw [← profile_filter_eq_take f O z hsorted]
  simp

theorem profile_take_allgood (f : α → β) (O : List α) (z : β)
    (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    ∀ v ∈ O.take (O.filter (fun w => decide (z ≤ f w))).length, z ≤ f v := by
  intro v hv
  exact ((mem_profile_take_iff f O z hsorted v).mp hv).2

variable [DecidableEq α]

@[simp] theorem descendingProfileOrder_toFinset (f : α → β) (O : List α) :
    (descendingProfileOrder f O).toFinset = O.toFinset := by
  ext v
  simp only [List.mem_toFinset]
  exact (descendingProfileOrder_perm f O).mem_iff

/-- The strict low-profile count is complementary to the upper-level-set size.
Nodup is exactly what identifies list length with finite-set cardinality. -/
theorem profile_filter_length_eq_sub_low_card (f : α → β) (O : List α)
    (z : β) (hO : O.Nodup) :
    (O.filter (fun v => decide (z ≤ f v))).length =
      O.length - (O.toFinset.filter (fun v => f v < z)).card := by
  have hcard : (O.toFinset.filter (fun v => z ≤ f v)).card =
      (O.filter (fun v => decide (z ≤ f v))).length := by
    rw [List.filter_toFinset]
    exact List.toFinset_card_of_nodup (hO.filter _)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := O.toFinset) (fun v => z ≤ f v)
  simp only [not_le] at hpartition
  rw [hcard, List.toFinset_card_of_nodup hO] at hpartition
  omega

/-- Rewriting the level-set prefix length using the strict bad-profile count. -/
theorem profile_orderPrefix_eq_filter (f : α → β) (O : List α) (z : β)
    (hO : O.Nodup) (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    orderPrefix O (O.length - (O.toFinset.filter (fun v => f v < z)).card) =
      O.toFinset.filter (fun v => z ≤ f v) := by
  rw [← profile_filter_length_eq_sub_low_card f O z hO]
  unfold orderPrefix
  rw [← profile_filter_eq_take f O z hsorted]
  simp

/-- All vertices in the cardinality-defined prefix meet the profile threshold. -/
theorem profile_orderPrefix_allgood (f : α → β) (O : List α) (z : β)
    (hO : O.Nodup) (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    ∀ v ∈ orderPrefix O
      (O.length - (O.toFinset.filter (fun w => f w < z)).card), z ≤ f v := by
  intro v hv
  rw [profile_orderPrefix_eq_filter f O z hO hsorted] at hv
  exact (Finset.mem_filter.mp hv).2

/-- Its complement is exactly the strict low-profile set, including at ties. -/
theorem profile_orderPrefix_complement (f : α → β) (O : List α) (z : β)
    (hO : O.Nodup) (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    O.toFinset \ orderPrefix O
      (O.length - (O.toFinset.filter (fun v => f v < z)).card) =
      O.toFinset.filter (fun v => f v < z) := by
  rw [profile_orderPrefix_eq_filter f O z hO hsorted]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hnot⟩
    exact ⟨hv, lt_of_not_ge (fun h => hnot ⟨hv, h⟩)⟩
  · rintro ⟨hv, hlt⟩
    exact ⟨hv, fun h => (not_le_of_gt hlt) h.2⟩

/-- The number of vertices outside the prefix is the candidate's exact `R(z)`. -/
theorem profile_orderPrefix_outside_card (f : α → β) (O : List α) (z : β)
    (hO : O.Nodup) (hsorted : O.Pairwise (fun u v => f v ≤ f u)) :
    (O.toFinset \ orderPrefix O
      (O.length - (O.toFinset.filter (fun v => f v < z)).card)).card =
      (O.toFinset.filter (fun v => f v < z)).card := by
  rw [profile_orderPrefix_complement f O z hO hsorted]

/-- One profile ordering has the exact good-prefix and bad-complement formulas
simultaneously for every threshold. No threshold-dependent sorting is used. -/
theorem descendingProfileOrder_all_thresholds (f : α → β) (O : List α)
    (hO : O.Nodup) :
    let P := descendingProfileOrder f O
    P.Nodup ∧ P.toFinset = O.toFinset ∧
      ∀ z : β,
        let R := (O.toFinset.filter (fun v => f v < z)).card
        let p := P.length - R
        p ≤ P.length ∧
        orderPrefix P p = O.toFinset.filter (fun v => z ≤ f v) ∧
        (∀ v ∈ orderPrefix P p, z ≤ f v) ∧
        (O.toFinset \ orderPrefix P p).card = R := by
  dsimp only
  have hnodup := descendingProfileOrder_nodup f O hO
  have hsorted := descendingProfileOrder_pairwise f O
  refine ⟨hnodup, descendingProfileOrder_toFinset f O, ?_⟩
  intro z
  refine ⟨Nat.sub_le _ _, ?_, ?_, ?_⟩
  · simpa only [descendingProfileOrder_toFinset] using
      profile_orderPrefix_eq_filter f (descendingProfileOrder f O) z hnodup hsorted
  · simpa only [descendingProfileOrder_toFinset] using
      profile_orderPrefix_allgood f (descendingProfileOrder f O) z hnodup hsorted
  · simpa only [descendingProfileOrder_toFinset] using
      profile_orderPrefix_outside_card f (descendingProfileOrder f O) z hnodup hsorted

/-- Finite-set form for downstream certificates: construct a single vertex order,
then every strict low-profile count determines its exact threshold prefix. -/
theorem exists_profile_order_all_thresholds (f : α → β) (Y : Finset α) :
    ∃ O : List α, O.Nodup ∧ O.toFinset = Y ∧
      O.Pairwise (fun u v => f v ≤ f u) ∧
      ∀ z : β,
        let R := (Y.filter (fun v => f v < z)).card
        let p := O.length - R
        p ≤ O.length ∧ orderPrefix O p = Y.filter (fun v => z ≤ f v) ∧
        (∀ v ∈ orderPrefix O p, z ≤ f v) ∧
        (Y \ orderPrefix O p).card = R := by
  obtain ⟨hnodup, hset, hall⟩ :=
    descendingProfileOrder_all_thresholds f Y.toList Y.nodup_toList
  refine ⟨descendingProfileOrder f Y.toList, hnodup, ?_,
    descendingProfileOrder_pairwise f Y.toList, ?_⟩
  · simp
  · simpa using hall

#print axioms descendingProfileOrder_perm
#print axioms descendingProfileOrder_pairwise
#print axioms descendingProfileOrder_nodup
#print axioms descendingProfileOrder_length
#print axioms profile_filter_eq_take
#print axioms mem_profile_take_iff
#print axioms profile_take_allgood
#print axioms descendingProfileOrder_toFinset
#print axioms profile_filter_length_eq_sub_low_card
#print axioms profile_orderPrefix_eq_filter
#print axioms profile_orderPrefix_allgood
#print axioms profile_orderPrefix_complement
#print axioms profile_orderPrefix_outside_card
#print axioms descendingProfileOrder_all_thresholds
#print axioms exists_profile_order_all_thresholds

end Erdos883Verified
