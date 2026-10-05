import Erdos883NeighborResources

namespace Erdos883Verified

/-- The relation-level count before the skeleton is removed. In particular,
reflexive relation witnesses are included, even though the associated simple
graph has no loops. -/
def rawCommon {V : Type*} (r : V → V → Prop) [DecidableRel r]
    (P : Finset V) (u v : V) : Finset V :=
  P.filter (fun w => r w u ∧ r w v)

/-- Outside the skeleton, raw relation witnesses yield both graph adjacencies.
The endpoint hypotheses justify removing loops only after skeleton deletion. -/
theorem relation_common_adj_of_not_mem {V : Type*} [DecidableEq V]
    (r : V → V → Prop) (S : Finset V) (u v w : V)
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∉ S)
    (hwu : r w u) (hwv : r w v) :
    (SimpleGraph.fromRel r).Adj w u ∧ (SimpleGraph.fromRel r).Adj w v := by
  constructor
  · exact (SimpleGraph.fromRel_adj r w u).mpr
      ⟨fun h => hw (h.symm ▸ hu), Or.inl hwu⟩
  · exact (SimpleGraph.fromRel_adj r w v).mpr
      ⟨fun h => hw (h.symm ▸ hv), Or.inl hwv⟩

/-- A relation-counted pool disjoint from the skeleton loses only vertices
absent from A. No irreflexivity assumption is imposed on the relation. -/
theorem disjoint_relation_pool_resource_bound {V : Type*} [DecidableEq V]
    (r : V → V → Prop) [DecidableRel r]
    (P A S : Finset V) (u v : V) {cost j : ℕ}
    (hu : u ∈ S) (hv : v ∈ S)
    (hPS : Disjoint P S) (hcost : (P \ A).card ≤ cost)
    (hsize : cost + j ≤ (rawCommon r P u v).card) :
    j ≤ (availableCommon (SimpleGraph.fromRel r) A S u v).card := by
  have hsub : rawCommon r P u v \ (P \ A) ⊆
      availableCommon (SimpleGraph.fromRel r) A S u v := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hraw, hnot⟩
    rcases Finset.mem_filter.mp hraw with ⟨hP, hrel⟩
    have hA : w ∈ A := by
      by_contra hn
      exact hnot (Finset.mem_sdiff.mpr ⟨hP, hn⟩)
    have hS : w ∉ S := fun hs => Finset.disjoint_left.mp hPS hP hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hA, hS⟩,
      relation_common_adj_of_not_mem r S u v w hu hv hS hrel.1 hrel.2⟩
  exact (resource_card_after_removal (rawCommon r P u v) (P \ A) hcost hsize).trans
    (Finset.card_le_card hsub)

/-- A general relation-counted pool loses missing A vertices and the skeleton.
Raw endpoints, including reflexive witnesses, are covered by this deletion. -/
theorem whole_relation_pool_resource_bound {V : Type*} [DecidableEq V]
    (r : V → V → Prop) [DecidableRel r]
    (P A S : Finset V) (u v : V) {cost j : ℕ}
    (hu : u ∈ S) (hv : v ∈ S)
    (hcost : (P \ A).card + S.card ≤ cost)
    (hsize : cost + j ≤ (rawCommon r P u v).card) :
    j ≤ (availableCommon (SimpleGraph.fromRel r) A S u v).card := by
  let removed := (P \ A) ∪ S
  have hremoved : removed.card ≤ cost :=
    (Finset.card_union_le (P \ A) S).trans hcost
  have hsub : rawCommon r P u v \ removed ⊆
      availableCommon (SimpleGraph.fromRel r) A S u v := by
    intro w hw
    rcases Finset.mem_sdiff.mp hw with ⟨hraw, hnot⟩
    rcases Finset.mem_filter.mp hraw with ⟨hP, hrel⟩
    have hA : w ∈ A := by
      by_contra hn
      exact hnot (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hP, hn⟩))
    have hS : w ∉ S := fun hs => hnot (Finset.mem_union_right _ hs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hA, hS⟩,
      relation_common_adj_of_not_mem r S u v w hu hv hS hrel.1 hrel.2⟩
  exact (resource_card_after_removal (rawCommon r P u v) removed hremoved hsize).trans
    (Finset.card_le_card hsub)

/-- Rankwise certificates use the original relation counts, before deleting
skeleton vertices or removing loops. They yield an odd cycle in the actual
induced simple graph on A. -/
theorem induced_oddCycle_of_relation_pool_certificates {V : Type*} [DecidableEq V]
    (r : V → V → Prop) [DecidableRel r] (A E U : Finset V)
    {k b cost : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V)
    (ho : Function.Injective o) (hoA : ∀ i, o i ∈ A)
    (hc : (SimpleGraph.fromRel r).Adj (o (Fin.last k)) (o 0))
    (hE : Disjoint E (Finset.univ.image o))
    (hb : (E \ A).card ≤ b)
    (hcost : (U \ A).card + (Finset.univ.image o).card ≤ cost)
    (hrank : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∃ bad : Finset (Fin k), bad.card < j ∧ ∀ i, i ∉ bad →
        b + j ≤ (rawCommon r E (o i.castSucc) (o i.succ)).card ∨
        cost + j ≤ (rawCommon r U (o i.castSucc) (o i.succ)).card) :
    2 * k + 1 ∈ ((SimpleGraph.fromRel r).induce (A : Set V)).oddCycleLengths := by
  let S := Finset.univ.image o
  let D : Fin k → Finset V := fun i =>
    availableCommon (SimpleGraph.fromRel r) A S (o i.castSucc) (o i.succ)
  have hoS : ∀ i, o i ∈ S := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  apply induced_oddCycle_of_rankwise_resources (SimpleGraph.fromRel r) A hk o ho hoA hc D
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
    · exact disjoint_relation_pool_resource_bound r E A S _ _
        (hoS _) (hoS _) hE hb h
    · exact whole_relation_pool_resource_bound r U A S _ _
        (hoS _) (hoS _) hcost h

#print axioms rawCommon
#print axioms relation_common_adj_of_not_mem
#print axioms disjoint_relation_pool_resource_bound
#print axioms whole_relation_pool_resource_bound
#print axioms induced_oddCycle_of_relation_pool_certificates

end Erdos883Verified
