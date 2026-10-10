import Erdos883SecondLinkCounts
import Erdos883SecondQuestionFinsets

/-! Finite bridge from a bipartite copy in an apex link to the exact
non-induced `(1,l,l)` graph target. It does not assert the full second question. -/

namespace Erdos883Second.Link

theorem containsTripartite_of_link_biclique {A L R : Finset ℕ} {a l : ℕ}
    (ha : a ∈ A) (hL : L ⊆ A) (hR : R ⊆ A)
    (haL : a ∉ L) (haR : a ∉ R) (hdis : Disjoint L R)
    (hLa : ∀ x ∈ L, Nat.Coprime a x)
    (hRa : ∀ r ∈ R, Nat.Coprime a r)
    (hbiclique : HasBiclique L R Nat.Coprime l) :
    ContainsTripartite A l := by
  obtain ⟨B, C, hBL, hCR, hBcard, hCcard, hBC⟩ := hbiclique
  let W : FinsetWitness A l := {
    apex := a
    left := B
    right := C
    apex_mem := ha
    left_subset := hBL.trans hL
    right_subset := hCR.trans hR
    left_card := hBcard
    right_card := hCcard
    apex_not_left := fun haB => haL (hBL haB)
    apex_not_right := fun haC => haR (hCR haC)
    disjoint := hdis.mono hBL hCR
    apex_left_coprime := fun x hx => hLa x (hBL hx)
    apex_right_coprime := fun r hr => hRa r (hCR hr)
    left_right_coprime := hBC }
  exact W.contains

theorem containsTripartite_of_link_high_degree {A L R H : Finset ℕ} {a l d : ℕ}
    (ha : a ∈ A) (hL : L ⊆ A) (hR : R ⊆ A)
    (haL : a ∉ L) (haR : a ∉ R) (hdis : Disjoint L R)
    (hLa : ∀ x ∈ L, Nat.Coprime a x)
    (hRa : ∀ r ∈ R, Nat.Coprime a r)
    (hH : H ⊆ R) (hdegree : ∀ r ∈ H, d ≤ (neighbors L Nat.Coprime r).card)
    (hcount : (l - 1) * L.card.choose l < H.card * d.choose l) :
    ContainsTripartite A l :=
  containsTripartite_of_link_biclique ha hL hR haL haR hdis hLa hRa
    (biclique_of_high_degree_count L R H Nat.Coprime l d hH hdegree hcount)

/-- Applying the rectangle count to an entire loopless apex link needs no
random partition: the two extracted parts are automatically disjoint. -/
theorem containsTripartite_of_irreflexive_link_biclique {A : Finset ℕ} {a l : ℕ}
    (E : ℕ → ℕ → Prop) (ha : a ∈ A)
    (hcoprime : ∀ x y, E x y → Nat.Coprime x y)
    (hirr : ∀ x, ¬ E x x)
    (hbiclique : HasBiclique (neighbors A E a) (neighbors A E a) E l) :
    ContainsTripartite A l := by
  classical
  obtain ⟨B, C, hBL, hCR, hBcard, hCcard, hBC⟩ := hbiclique
  have hmem {x : ℕ} (hx : x ∈ neighbors A E a) : x ∈ A ∧ E x a :=
    Finset.mem_filter.mp hx
  let W : FinsetWitness A l := {
    apex := a
    left := B
    right := C
    apex_mem := ha
    left_subset := fun x hx => (hmem (hBL hx)).1
    right_subset := fun x hx => (hmem (hCR hx)).1
    left_card := hBcard
    right_card := hCcard
    apex_not_left := fun haB => hirr a (hmem (hBL haB)).2
    apex_not_right := fun haC => hirr a (hmem (hCR haC)).2
    disjoint := Finset.disjoint_left.mpr (fun x hxB hxC => hirr x (hBC x hxB x hxC))
    apex_left_coprime := fun x hx => (hcoprime x a (hmem (hBL hx)).2).symm
    apex_right_coprime := fun x hx => (hcoprime x a (hmem (hCR hx)).2).symm
    left_right_coprime := fun x hx y hy => hcoprime x y (hBC x hx y hy) }
  exact W.contains

#print axioms containsTripartite_of_link_biclique
#print axioms containsTripartite_of_link_high_degree
#print axioms containsTripartite_of_irreflexive_link_biclique

end Erdos883Second.Link
