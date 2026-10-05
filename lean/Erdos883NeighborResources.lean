import Erdos883Rankwise

namespace Erdos883Verified

/-- The raw common neighbors in a specified finite pool. -/
def commonIn {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (u v : V) : Finset V :=
  P.filter (fun w => G.Adj w u ∧ G.Adj w v)

/-- Available connectors must lie in A and outside the skeleton S. -/
def availableCommon {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A S : Finset V) (u v : V) : Finset V :=
  commonIn G (A \ S) u v

/-- A pool disjoint from the skeleton loses only vertices absent from A.
This is the even-pool resource calculation. -/
theorem disjoint_pool_resource_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P A S : Finset V) (u v : V) {cost j : ℕ}
    (hPS : Disjoint P S) (hcost : (P \ A).card ≤ cost)
    (hsize : cost + j ≤ (commonIn G P u v).card) :
    j ≤ (availableCommon G A S u v).card := by
  have hsub : commonIn G P u v \ (P \ A) ⊆ availableCommon G A S u v := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hraw, hnot⟩
    rcases Finset.mem_filter.mp hraw with ⟨hP, hadj⟩
    have hA : w ∈ A := by
      by_contra hn
      exact hnot (Finset.mem_sdiff.mpr ⟨hP, hn⟩)
    have hS : w ∉ S := fun hs => Finset.disjoint_left.mp hPS hP hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hA, hS⟩, hadj⟩
  exact (resource_card_after_removal (commonIn G P u v) (P \ A) hcost hsize).trans
    (Finset.card_le_card hsub)

/-- A general pool loses missing A vertices and all skeleton vertices.
This is the whole-pool resource calculation. -/
theorem whole_pool_resource_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P A S : Finset V) (u v : V) {cost j : ℕ}
    (hcost : (P \ A).card + S.card ≤ cost)
    (hsize : cost + j ≤ (commonIn G P u v).card) :
    j ≤ (availableCommon G A S u v).card := by
  let removed := (P \ A) ∪ S
  have hremoved : removed.card ≤ cost :=
    (Finset.card_union_le (P \ A) S).trans hcost
  have hsub : commonIn G P u v \ removed ⊆ availableCommon G A S u v := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hraw, hnot⟩
    rcases Finset.mem_filter.mp hraw with ⟨hP, hadj⟩
    have hA : w ∈ A := by
      by_contra hn
      exact hnot (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hP, hn⟩))
    have hS : w ∉ S := fun hs => hnot (Finset.mem_union_right _ hs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hA, hS⟩, hadj⟩
  exact (resource_card_after_removal (commonIn G P u v) removed hremoved hsize).trans
    (Finset.card_le_card hsub)

/-- Hall is performed on actual V-valued resources, then all selected vertices
are embedded into the induced graph on A. -/
theorem induced_oddCycle_of_rankwise_resources {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V)
    {k : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V) (ho : Function.Injective o)
    (hoA : ∀ i, o i ∈ A) (hc : G.Adj (o (Fin.last k)) (o 0))
    (D : Fin k → Finset V) (hDA : ∀ i, D i ⊆ A)
    (hleft : ∀ i w, w ∈ D i → G.Adj w (o i.castSucc))
    (hright : ∀ i w, w ∈ D i → G.Adj w (o i.succ))
    (hdisjoint : ∀ i w, w ∈ D i → ∀ z, o z ≠ w)
    (hrank : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∃ bad : Finset (Fin k), bad.card < j ∧ ∀ i, i ∉ bad → j ≤ (D i).card) :
    2 * k + 1 ∈ (G.induce (A : Set V)).oddCycleLengths := by
  obtain ⟨w, hw, hwD⟩ := hall_of_rankwise_exceptions D (by
    intro j hj hjmax
    exact hrank j hj (by simpa using hjmax))
  let oA : Fin (k + 1) → (A : Set V) := fun i => ⟨o i, hoA i⟩
  let wA : Fin k → (A : Set V) := fun i => ⟨w i, hDA i (hwD i)⟩
  apply oddCycleLength_of_alternating (G.induce (A : Set V)) hk oA wA
  · intro i j he
    exact ho (congrArg Subtype.val he)
  · intro i j he
    exact hw (congrArg Subtype.val he)
  · intro z i he
    exact hdisjoint i (w i) (hwD i) z (congrArg Subtype.val he)
  · intro i
    exact hleft i (w i) (hwD i)
  · intro i
    exact hright i (w i) (hwD i)
  · exact hc

#print axioms disjoint_pool_resource_bound
#print axioms whole_pool_resource_bound
#print axioms induced_oddCycle_of_rankwise_resources

/-- The two resource alternatives may vary by rank and gap. They still certify
one actual connector family and hence a cycle inside the induced graph on A. -/
theorem induced_oddCycle_of_pool_certificates {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A E U : Finset V)
    {k b cost : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V)
    (ho : Function.Injective o) (hoA : ∀ i, o i ∈ A)
    (hc : G.Adj (o (Fin.last k)) (o 0))
    (hE : Disjoint E (Finset.univ.image o))
    (hb : (E \ A).card ≤ b)
    (hcost : (U \ A).card + (Finset.univ.image o).card ≤ cost)
    (hrank : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∃ bad : Finset (Fin k), bad.card < j ∧ ∀ i, i ∉ bad →
        b + j ≤ (commonIn G E (o i.castSucc) (o i.succ)).card ∨
        cost + j ≤ (commonIn G U (o i.castSucc) (o i.succ)).card) :
    2 * k + 1 ∈ (G.induce (A : Set V)).oddCycleLengths := by
  let S := Finset.univ.image o
  let D : Fin k → Finset V := fun i => availableCommon G A S (o i.castSucc) (o i.succ)
  apply induced_oddCycle_of_rankwise_resources G A hk o ho hoA hc D
  · intro i w hw
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).1
  · intro i w hw
    exact (Finset.mem_filter.mp hw).2.1
  · intro i w hw
    exact (Finset.mem_filter.mp hw).2.2
  · intro i w hw z he
    have hn : w ∉ S := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    exact hn (Finset.mem_image.mpr ⟨z, Finset.mem_univ z, he⟩)
  · intro j hj hjmax
    obtain ⟨bad, hbad, hgood⟩ := hrank j hj hjmax
    refine ⟨bad, hbad, ?_⟩
    intro i hi
    rcases hgood i hi with h | h
    · exact disjoint_pool_resource_bound G E A S _ _ hE hb h
    · exact whole_pool_resource_bound G U A S _ _ hcost h

#print axioms induced_oddCycle_of_pool_certificates

end Erdos883Verified
