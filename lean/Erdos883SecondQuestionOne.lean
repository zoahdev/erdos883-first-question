import Erdos883SecondQuestion

namespace Erdos883Second

/-- A genuine three-cycle is exactly enough for the case `l = 1`. -/
theorem contains_one_of_triangle {A : Finset ℕ}
    (h : 3 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).cycleLengths) :
    ContainsTripartite A 1 := by
  classical
  obtain ⟨a, w, hw, hlen⟩ := h
  have hinj := hw.getVert_injOn
  have hne {i j : ℕ} (hi : 1 ≤ i) (hi3 : i ≤ 3)
      (hj : 1 ≤ j) (hj3 : j ≤ 3) (hij : i ≠ j) :
      (w.getVert i).val ≠ (w.getVert j).val := by
    intro he
    exact hij (hinj ⟨hi, by omega⟩ ⟨hj, by omega⟩ (Subtype.ext he))
  have hc {i : ℕ} (hi : i < 3) :
      Nat.Coprime (w.getVert i).val (w.getVert (i + 1)).val := by
    have hadj := w.adj_getVert_succ (i := i) (by omega)
    exact hadj.2.elim id Nat.Coprime.symm
  have h30 : w.getVert 3 = w.getVert 0 := by
    rw [← hlen, w.getVert_length, w.getVert_zero]
  let W : Witness A 1 := {
    apex := (w.getVert 3).val
    left := fun _ => (w.getVert 1).val
    right := fun _ => (w.getVert 2).val
    apex_mem := (w.getVert 3).property
    left_mem := fun _ => (w.getVert 1).property
    right_mem := fun _ => (w.getVert 2).property
    left_injective := fun _ _ _ => Subsingleton.elim _ _
    right_injective := fun _ _ _ => Subsingleton.elim _ _
    apex_left_ne := fun _ => hne (by omega) (by omega) (by omega) (by omega) (by omega)
    apex_right_ne := fun _ => hne (by omega) (by omega) (by omega) (by omega) (by omega)
    left_right_ne := fun _ _ => hne (by omega) (by omega) (by omega) (by omega) (by omega)
    apex_left_coprime := fun _ => by simpa [h30] using hc (i := 0) (by omega)
    apex_right_coprime := fun _ => (hc (i := 2) (by omega)).symm
    left_right_coprime := fun _ _ => hc (i := 1) (by omega) }
  exact W.contains

/-- The first question implies the fixed `l=1` part of the second question,
with the explicit sufficiently-large threshold `N=6`. This says nothing about
`l>=2`, and does not assert the full second question. -/
theorem firstQuestion_implies_secondQuestion_one
    (hFirst : Erdos883Target.FirstQuestion) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
        ContainsTripartite A 1 := by
  refine ⟨6, ?_⟩
  intro n hn A hA hcard
  have htriangle := hFirst n A hA hcard 3 (by decide) (by omega) (by omega)
  exact contains_one_of_triangle htriangle.1

#print axioms contains_one_of_triangle
#print axioms firstQuestion_implies_secondQuestion_one

end Erdos883Second
