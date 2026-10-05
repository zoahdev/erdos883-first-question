import Erdos883OrderedHall
import Erdos883AlternatingCycle

namespace Erdos883Verified

/-- Each rank may use a different exceptional set. All certificates refer to the
same actual resource family D, so Hall still supplies simultaneous representatives. -/
theorem hall_of_rankwise_exceptions {ι α : Type*} [Fintype ι]
    (D : ι → Finset α)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card ι →
      ∃ bad : Finset ι, bad.card < j ∧ ∀ i, i ∉ bad → j ≤ (D i).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ D i := by
  classical
  apply Erdos883.ordered_hall D
  intro j hj hjmax
  obtain ⟨bad, hbad, hgood⟩ := h j hj hjmax
  have hsubset : (Finset.univ.filter fun i => (D i).card < j) ⊆ bad := by
    intro i hi
    by_contra hnot
    exact Nat.not_lt_of_ge (hgood i hnot) (Finset.mem_filter.mp hi).2
  exact lt_of_le_of_lt (Finset.card_le_card hsubset) hbad

#print axioms hall_of_rankwise_exceptions

/-- Deleting at most `cost` vertices from a sufficiently large neighbor set
leaves at least the current rank many available representatives. -/
theorem resource_card_after_removal {α : Type*} [DecidableEq α]
    (neighbors removed : Finset α) {cost j : ℕ}
    (hremoved : removed.card ≤ cost) (hsize : cost + j ≤ neighbors.card) :
    j ≤ (neighbors \ removed).card := by
  have h := Finset.le_card_sdiff removed neighbors
  omega

/-- The complete graph-theoretic assembly: rank-dependent certificates for
connector sets yield the requested odd cycle on one fixed skeleton. -/
theorem oddCycle_of_rankwise_resources {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V) (ho : Function.Injective o)
    (hc : G.Adj (o (Fin.last k)) (o 0)) (D : Fin k → Finset V)
    (hleft : ∀ i w, w ∈ D i → G.Adj w (o i.castSucc))
    (hright : ∀ i w, w ∈ D i → G.Adj w (o i.succ))
    (hdisjoint : ∀ i w, w ∈ D i → ∀ z, o z ≠ w)
    (hrank : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∃ bad : Finset (Fin k), bad.card < j ∧ ∀ i, i ∉ bad → j ≤ (D i).card) :
    2 * k + 1 ∈ G.oddCycleLengths := by
  obtain ⟨w, hw, hwD⟩ := hall_of_rankwise_exceptions D (by
    intro j hj hjmax
    exact hrank j hj (by simpa using hjmax))
  exact oddCycleLength_of_alternating G hk o w ho hw
    (fun z i => hdisjoint i (w i) (hwD i) z)
    (fun i => hleft i (w i) (hwD i))
    (fun i => hright i (w i) (hwD i)) hc

#print axioms resource_card_after_removal
#print axioms oddCycle_of_rankwise_resources

end Erdos883Verified
