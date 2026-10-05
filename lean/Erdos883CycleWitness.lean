import Erdos883CycleLengths
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace Erdos883Verified

/-- An injective cyclic sequence of adjacent vertices gives a cycle of exactly n edges. -/
theorem cycleLength_of_injective_successors {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (hn : 2 < n) [NeZero n] (f : Fin n → V)
    (hinj : Function.Injective f) (hedge : ∀ i, G.Adj (f i) (f (i + 1))) :
    n ∈ G.cycleLengths := by
  apply (SimpleGraph.cycleGraph_isContained_iff hn).mp
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  rcases SimpleGraph.cycleGraph_adj'.mp hij with h | h
  · have he : i - j = 1 := Fin.ext (h.trans hone.symm)
    have he' : i = j + 1 := by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    rw [he']
    exact (hedge j).symm
  · have he : j - i = 1 := Fin.ext (h.trans hone.symm)
    have he' : j = i + 1 := by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    rw [he']
    exact hedge i

theorem oddCycleLength_of_injective_successors {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (hn : 2 < n) (hodd : Odd n) [NeZero n] (f : Fin n → V)
    (hinj : Function.Injective f) (hedge : ∀ i, G.Adj (f i) (f (i + 1))) :
    n ∈ G.oddCycleLengths :=
  ⟨cycleLength_of_injective_successors G hn f hinj hedge, hodd⟩

#print axioms cycleLength_of_injective_successors
#print axioms oddCycleLength_of_injective_successors
end Erdos883Verified
