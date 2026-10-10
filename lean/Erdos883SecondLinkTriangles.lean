import Erdos883SecondLinkDensity
import Erdos883SecondLinkTripartite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Uniform ordered-triangle sparsity from absence of `(1,l,l)`.
Every ordered triple is counted once, by its apex and the two ordered link
vertices. Irreflexivity forces three distinct vertices. -/

namespace Erdos883Second.Link

open scoped BigOperators

variable {α : Type*}

noncomputable def orderedTriangleCount (A : Finset α) (E : α → α → Prop) : ℕ :=
  ∑ a ∈ A, ∑ r ∈ neighbors A E a, (neighbors (neighbors A E a) E r).card

theorem orderedTriangleCount_small_of_no_link_biclique (A : Finset α)
    (E : α → α → Prop) (n k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : A.card ≤ n) (hn : denseThreshold k l ≤ n)
    (hno : ∀ a ∈ A, ¬ HasBiclique (neighbors A E a) (neighbors A E a) E l) :
    k * orderedTriangleCount A E < n ^ 3 := by
  classical
  have hnpos : 0 < n := by
    have hmax : 1 ≤ max l ((l - 1) * (8 * k) ^ l + 1) :=
      hl.trans (Nat.le_max_left _ _)
    have htpos : 0 < denseThreshold k l :=
      Nat.mul_pos (by omega) (by omega)
    omega
  have hsqpos : 0 < n * n := Nat.mul_pos hnpos hnpos
  have hbound : k * orderedTriangleCount A E ≤ A.card * (n * n - 1) := by
    unfold orderedTriangleCount
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _a ∈ A, (n * n - 1) := by
        apply Finset.sum_le_sum
        intro a ha
        have hN : (neighbors A E a).card ≤ n := (neighbors_card_le A E a).trans hA
        have hh := edge_count_small_of_no_biclique (neighbors A E a)
          (neighbors A E a) E n k l hk hl hN hN hn (hno a ha)
        omega
      _ = _ := by simp
  calc
    _ ≤ A.card * (n * n - 1) := hbound
    _ ≤ n * (n * n - 1) := Nat.mul_le_mul_right _ hA
    _ < n * (n * n) := Nat.mul_lt_mul_of_pos_left (by omega) hnpos
    _ = _ := by ring

/-- Exact coprime adjacency, with distinctness explicitly included. -/
def coprimeRelation (x y : ℕ) : Prop := x ≠ y ∧ Nat.Coprime x y

theorem ordered_coprime_triangles_small_of_no_tripartite (A : Finset ℕ)
    (n k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : A.card ≤ n) (hn : denseThreshold k l ≤ n)
    (hno : ¬ ContainsTripartite A l) :
    k * orderedTriangleCount A coprimeRelation < n ^ 3 := by
  apply orderedTriangleCount_small_of_no_link_biclique A coprimeRelation n k l hk hl hA hn
  intro a ha hbiclique
  exact hno (containsTripartite_of_irreflexive_link_biclique coprimeRelation ha
    (fun _ _ h => h.2) (fun _ h => h.1 rfl) hbiclique)

/-- Complete uniform quantifier interface: for every fixed `l` and reciprocal
density `1/k`, one explicit threshold works for every set with at most `n`
vertices. No sufficiently-large exception depends on the particular set. -/
theorem ordered_coprime_triangles_eventually_small (l k : ℕ)
    (hl : 1 ≤ l) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, A.card ≤ n →
      ¬ ContainsTripartite A l → k * orderedTriangleCount A coprimeRelation < n ^ 3 := by
  refine ⟨denseThreshold k l, ?_⟩
  intro n hn A hA hno
  exact ordered_coprime_triangles_small_of_no_tripartite A n k l hk hl hA hn hno

#print axioms orderedTriangleCount_small_of_no_link_biclique
#print axioms ordered_coprime_triangles_small_of_no_tripartite
#print axioms ordered_coprime_triangles_eventually_small

end Erdos883Second.Link
