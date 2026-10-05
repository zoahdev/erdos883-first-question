import Erdos883ParityCounts
import Erdos883RetentionOrder

namespace Erdos883Verified

theorem evenUniverse_mono {n u : ℕ} (h : n ≤ u) : evenUniverse n ⊆ evenUniverse u := by
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hi, he⟩
  rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans h⟩, he⟩

theorem orderPrefix_card {α : Type*} [DecidableEq α] (O : List α)
    (hO : O.Nodup) {k : ℕ} (hk : k ≤ O.length) : (orderPrefix O k).card = k := by
  rw [orderPrefix, List.toFinset_card_of_nodup (hO.take), List.length_take,
    Nat.min_eq_left hk]

theorem outside_orderPrefix_card {α : Type*} [DecidableEq α] (O : List α)
    (hO : O.Nodup) {k : ℕ} (hk : k ≤ O.length) :
    (O.toFinset \ orderPrefix O k).card = O.length - k := by
  have hsub : orderPrefix O k ⊆ O.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
  rw [Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup hO,
    orderPrefix_card O hO hk]

/-- An injective skeleton inherits every retained-set exceptional-vertex bound. -/
theorem skeleton_outside_card_le {α : Type*} [DecidableEq α] {m : ℕ}
    (o : Fin m → α) (ho : Function.Injective o) (Y P : Finset α)
    (hoY : ∀ i, o i ∈ Y) :
    (Finset.univ.filter (fun i => o i ∉ P)).card ≤ (Y \ P).card := by
  rw [← Finset.card_image_of_injective _ ho]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_sdiff.mpr ⟨hoY i, (Finset.mem_filter.mp hi).2⟩

theorem dense_missing_even_bound {n : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card) :
    (evenUniverse n \ A).card ≤ halfOdds n - retainedOdds n := by
  have h := dense_set_odd_surplus A hA hdense
  have hc := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := oddUniverse n))
  rw [oddUniverse_card] at hc
  omega

/-- Uniform interval cost includes every missing vertex and the entire skeleton. -/
theorem interval_whole_pool_cost {L n U k : ℕ} (A : Finset ℕ)
    (hLn : L ≤ n) (hnU : n ≤ U) (hA : A ⊆ Finset.Icc 1 n)
    (hdense : threshold n < A.card) (hk : k ≤ maxHalfLength n)
    (o : Fin (k + 1) → ℕ) (ho : Function.Injective o) :
    (Finset.Icc 1 L \ A).card + (Finset.univ.image o).card ≤
      U - threshold U + maxHalfLength U := by
  have hsub : Finset.Icc 1 L \ A ⊆ Finset.Icc 1 n \ A := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hi, hn⟩
    rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans hLn⟩, hn⟩
  have hmissing := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hA] at hmissing
  have hcardA : A.card ≤ n := by
    have h := Finset.card_le_card hA
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hcost := resource_cost_bound hnU hcardA hdense hk
  have hskel : (Finset.univ.image o).card = k + 1 := by
    rw [Finset.card_image_of_injective _ ho, Finset.card_univ, Fintype.card_fin]
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hmissing
  rw [hskel]
  omega

#print axioms evenUniverse_mono
#print axioms orderPrefix_card
#print axioms outside_orderPrefix_card
#print axioms skeleton_outside_card_le
#print axioms dense_missing_even_bound
#print axioms interval_whole_pool_cost
end Erdos883Verified
