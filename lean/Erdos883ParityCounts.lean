import Arithmetic
import Erdos883Smoothing
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Ring.Parity

namespace Erdos883Verified

def oddUniverse (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter Odd
def evenUniverse (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter Even

theorem oddUniverse_eq_image (n : ℕ) :
    oddUniverse n = (Finset.range ((n + 1) / 2)).image (fun i => 2 * i + 1) := by
  ext v
  simp only [oddUniverse, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hvpos, hvn⟩, ⟨k, hk⟩⟩
    exact ⟨k, by omega, hk.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩

theorem evenUniverse_eq_image (n : ℕ) :
    evenUniverse n = (Finset.range (n / 2)).image (fun i => 2 * (i + 1)) := by
  ext v
  simp only [evenUniverse, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hvpos, hvn⟩, ⟨k, hk⟩⟩
    exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k + 1, by omega⟩⟩

theorem oddUniverse_card (n : ℕ) : (oddUniverse n).card = halfOdds n := by
  rw [oddUniverse_eq_image, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro a b h
    dsimp at h
    omega

theorem evenUniverse_card (n : ℕ) : (evenUniverse n).card = n / 2 := by
  rw [evenUniverse_eq_image, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro a b h
    dsimp at h
    omega

theorem even_odd_disjoint (n : ℕ) : Disjoint (evenUniverse n) (oddUniverse n) := by
  apply Finset.disjoint_left.mpr
  intro v he ho
  rcases (Finset.mem_filter.mp he).2 with ⟨a, ha⟩
  rcases (Finset.mem_filter.mp ho).2 with ⟨b, hb⟩
  omega

theorem even_odd_union (n : ℕ) : evenUniverse n ∪ oddUniverse n = Finset.Icc 1 n := by
  ext v
  simp only [evenUniverse, oddUniverse, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases Nat.even_or_odd v with he | ho
    · exact Or.inl ⟨h, he⟩
    · exact Or.inr ⟨h, ho⟩

theorem oddUniverse_mono {n u : ℕ} (h : n ≤ u) : oddUniverse n ⊆ oddUniverse u := by
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hi, ho⟩
  rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans h⟩, ho⟩

theorem threshold_ge_evens (n : ℕ) : n / 2 ≤ threshold n := by
  unfold threshold
  omega

/-- Dense A contains M(n) plus one extra selected odd for every missing even. -/
theorem dense_set_odd_surplus {n : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card) :
    retainedOdds n + (evenUniverse n \ A).card ≤ (A ∩ oddUniverse n).card := by
  have hpartition : A ⊆ evenUniverse n ∪ oddUniverse n := by
    rwa [even_odd_union]
  have h := density_gives_odd_surplus A (evenUniverse n) (oddUniverse n)
    (threshold n) hpartition (even_odd_disjoint n)
    (by simpa only [evenUniverse_card] using threshold_ge_evens n) hdense
  simpa only [evenUniverse_card, ← retained_formula] using h

#print axioms oddUniverse_eq_image
#print axioms evenUniverse_eq_image
#print axioms oddUniverse_card
#print axioms evenUniverse_card
#print axioms even_odd_disjoint
#print axioms even_odd_union
#print axioms oddUniverse_mono
#print axioms threshold_ge_evens
#print axioms dense_set_odd_surplus
end Erdos883Verified
