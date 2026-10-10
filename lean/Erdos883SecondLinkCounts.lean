import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Independent finite graph-counting interface for the far-U branch.

`E` is an arbitrary cross-part relation, so no graph-theoretic extremal result
is imported as a premise.  We double-count stars with `l` distinct left
vertices. Absence of a complete `(l,l)` rectangle bounds the total star count.
These finite lemmas do not assert the complete second question.
-/

namespace Erdos883Second.Link

open scoped BigOperators

variable {α β : Type*}

attribute [local instance] Classical.propDecidable

noncomputable def neighbors (L : Finset α) (E : α → β → Prop) (r : β) : Finset α := by
  classical
  exact L.filter (fun x => E x r)

noncomputable def commonNeighbors (R : Finset β) (E : α → β → Prop)
    (B : Finset α) : Finset β := by
  classical
  exact R.filter (fun r => ∀ x ∈ B, E x r)

noncomputable def highCenters (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (d : ℕ) : Finset β := by
  classical
  exact R.filter (fun r => d ≤ (neighbors L E r).card)

theorem neighbors_card_le (L : Finset α) (E : α → β → Prop) (r : β) :
    (neighbors L E r).card ≤ L.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Splitting right vertices at degree `d` bounds the edge count using the
actual number of high-degree centers. The displayed low-degree loss is coarse
but valid also at `d=0`. -/
theorem edge_count_le_highCenters (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (d : ℕ) :
    (∑ r ∈ R, (neighbors L E r).card) ≤
      (highCenters L R E d).card * L.card + R.card * (d - 1) := by
  classical
  calc
    _ ≤ ∑ r ∈ R, if d ≤ (neighbors L E r).card then L.card else d - 1 := by
      apply Finset.sum_le_sum
      intro r hr
      split_ifs with h
      · exact neighbors_card_le L E r
      · omega
    _ = (highCenters L R E d).card * L.card +
        (R.filter (fun r => ¬ d ≤ (neighbors L E r).card)).card * (d - 1) := by
      rw [Finset.sum_ite]
      simp [highCenters]
    _ ≤ _ := by
      have hc : (R.filter (fun r => ¬ d ≤ (neighbors L E r).card)).card ≤ R.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      exact Nat.add_le_add_left (Nat.mul_le_mul_right (d - 1) hc) _

/-- A complete cross-part rectangle with exactly `l` vertices on each side.
Within-part edges are unrestricted; thus this is a non-induced copy. -/
def HasBiclique (L : Finset α) (R : Finset β) (E : α → β → Prop) (l : ℕ) : Prop :=
  ∃ B C, B ⊆ L ∧ C ⊆ R ∧ B.card = l ∧ C.card = l ∧
    ∀ x ∈ B, ∀ r ∈ C, E x r

theorem powersetCard_neighbors (L : Finset α) (E : α → β → Prop) (r : β) (l : ℕ) :
    (neighbors L E r).powersetCard l =
      (L.powersetCard l).filter (fun B => ∀ x ∈ B, E x r) := by
  classical
  ext B
  simp only [neighbors, Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hB, hcard⟩
    exact ⟨⟨fun x hx => (Finset.mem_filter.mp (hB hx)).1, hcard⟩,
      fun x hx => (Finset.mem_filter.mp (hB hx)).2⟩
  · rintro ⟨⟨hB, hcard⟩, hE⟩
    exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hB hx, hE x hx⟩, hcard⟩

/-- Double-count stars, first by their right center and then by their left
`l`-element leaf set. Every leaf is distinct because it is a finite subset. -/
theorem star_count_eq (L : Finset α) (R : Finset β) (E : α → β → Prop) (l : ℕ) :
    (∑ r ∈ R, (neighbors L E r).card.choose l) =
      ∑ B ∈ L.powersetCard l, (commonNeighbors R E B).card := by
  classical
  calc
    _ = ∑ r ∈ R, ∑ B ∈ L.powersetCard l, if (∀ x ∈ B, E x r) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.card_powersetCard, powersetCard_neighbors,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ B ∈ L.powersetCard l, ∑ r ∈ R, if (∀ x ∈ B, E x r) then 1 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      simp only [commonNeighbors, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem biclique_of_commonNeighbors_card (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (l : ℕ) {B : Finset α}
    (hB : B ∈ L.powersetCard l) (hcommon : l ≤ (commonNeighbors R E B).card) :
    HasBiclique L R E l := by
  classical
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hcommon
  obtain ⟨hBL, hBcard⟩ := Finset.mem_powersetCard.mp hB
  refine ⟨B, C, hBL, ?_, hBcard, hCcard, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp (hCsub hr)).1
  · intro x hx r hr
    exact (Finset.mem_filter.mp (hCsub hr)).2 x hx

theorem commonNeighbors_card_lt_of_no_biclique (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (l : ℕ) (hno : ¬ HasBiclique L R E l)
    {B : Finset α} (hB : B ∈ L.powersetCard l) :
    (commonNeighbors R E B).card < l := by
  by_contra hn
  exact hno (biclique_of_commonNeighbors_card L R E l hB (Nat.le_of_not_gt hn))

/-- The finite upper half of the dense-link star argument. -/
theorem star_count_le_of_no_biclique (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (l : ℕ) (hno : ¬ HasBiclique L R E l) :
    (∑ r ∈ R, (neighbors L E r).card.choose l) ≤ (l - 1) * L.card.choose l := by
  classical
  rw [star_count_eq]
  calc
    _ ≤ ∑ _B ∈ L.powersetCard l, (l - 1) := by
      apply Finset.sum_le_sum
      intro B hB
      have hh := commonNeighbors_card_lt_of_no_biclique L R E l hno hB
      omega
    _ = _ := by simp [Nat.mul_comm]

/-- Any strict excess over the no-rectangle star bound constructs a full
non-induced `(l,l)` bipartite copy. -/
theorem biclique_of_star_count_gt (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (l : ℕ)
    (hstars : (l - 1) * L.card.choose l <
      ∑ r ∈ R, (neighbors L E r).card.choose l) :
    HasBiclique L R E l := by
  by_contra hno
  exact (not_lt_of_ge (star_count_le_of_no_biclique L R E l hno)) hstars

/-- A finite set of high-degree centers gives an explicit lower star count. -/
theorem high_degree_star_count_le (L : Finset α) (R H : Finset β)
    (E : α → β → Prop) (l d : ℕ) (hH : H ⊆ R)
    (hdegree : ∀ r ∈ H, d ≤ (neighbors L E r).card) :
    H.card * d.choose l ≤ ∑ r ∈ R, (neighbors L E r).card.choose l := by
  classical
  calc
    _ = ∑ _r ∈ H, d.choose l := by simp
    _ ≤ ∑ r ∈ H, (neighbors L E r).card.choose l := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.choose_le_choose l (hdegree r hr)
    _ ≤ _ := Finset.sum_le_sum_of_subset hH

/-- The exact finite high-degree obstruction used in the common-neighbor
argument; no density limit or asymptotic theorem is hidden in this lemma. -/
theorem high_degree_bound_of_no_biclique (L : Finset α) (R H : Finset β)
    (E : α → β → Prop) (l d : ℕ) (hH : H ⊆ R)
    (hdegree : ∀ r ∈ H, d ≤ (neighbors L E r).card)
    (hno : ¬ HasBiclique L R E l) :
    H.card * d.choose l ≤ (l - 1) * L.card.choose l :=
  (high_degree_star_count_le L R H E l d hH hdegree).trans
    (star_count_le_of_no_biclique L R E l hno)

/-- Concrete degree and center counts suffice to construct a biclique. -/
theorem biclique_of_high_degree_count (L : Finset α) (R H : Finset β)
    (E : α → β → Prop) (l d : ℕ) (hH : H ⊆ R)
    (hdegree : ∀ r ∈ H, d ≤ (neighbors L E r).card)
    (hcount : (l - 1) * L.card.choose l < H.card * d.choose l) :
    HasBiclique L R E l :=
  biclique_of_star_count_gt L R E l
    (hcount.trans_le (high_degree_star_count_le L R H E l d hH hdegree))

#print axioms star_count_eq
#print axioms edge_count_le_highCenters
#print axioms star_count_le_of_no_biclique
#print axioms biclique_of_star_count_gt
#print axioms high_degree_bound_of_no_biclique
#print axioms biclique_of_high_degree_count

end Erdos883Second.Link
