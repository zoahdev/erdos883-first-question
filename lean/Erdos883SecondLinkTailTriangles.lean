import Erdos883SecondLinkTailPairs
import Erdos883SecondLinkRealDensity

/-! Finite tuple representation of ordered triangles and the cutoff tail
error for small-prime-disjoint triples of actual integers. -/

namespace Erdos883Second.Link

open scoped BigOperators

variable {α : Type*}

noncomputable def triangleTuples (A : Finset α) (E : α → α → Prop) :
    Finset (α × α × α) := by
  classical
  exact (A ×ˢ (A ×ˢ A)).filter
    (fun t => E t.2.1 t.1 ∧ E t.2.2 t.1 ∧ E t.2.2 t.2.1)

theorem triangleTuples_card_eq (A : Finset α) (E : α → α → Prop) :
    (triangleTuples A E).card = orderedTriangleCount A E := by
  classical
  simp only [triangleTuples, orderedTriangleCount, neighbors, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : E b a <;> simp [hab, ite_and]

noncomputable def relationDifferencePairs (A : Finset α)
    (E F : α → α → Prop) : Finset (α × α) := by
  classical
  exact (A ×ˢ A).filter (fun xy => E xy.1 xy.2 ∧ ¬ F xy.1 xy.2)

noncomputable def frontLift (A : Finset α) (B : Finset (α × α)) :
    Finset (α × α × α) := by
  classical
  exact (B ×ˢ A).image (fun t => (t.1.2, (t.1.1, t.2)))

noncomputable def outerLift (A : Finset α) (B : Finset (α × α)) :
    Finset (α × α × α) := by
  classical
  exact (B ×ˢ A).image (fun t => (t.1.2, (t.2, t.1.1)))

noncomputable def backLift (A : Finset α) (B : Finset (α × α)) :
    Finset (α × α × α) := by
  classical
  exact (A ×ˢ B).image (fun t => (t.1, (t.2.2, t.2.1)))

theorem triangleTuples_card_le_of_relationDifference (A : Finset α)
    (E F : α → α → Prop) :
    (triangleTuples A E).card ≤ (triangleTuples A F).card +
      3 * A.card * (relationDifferencePairs A E F).card := by
  classical
  let B := relationDifferencePairs A E F
  have hsub : triangleTuples A E ⊆
      ((triangleTuples A F ∪ frontLift A B) ∪ outerLift A B) ∪ backLift A B := by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨hmem, hab, hac, hbc⟩ := Finset.mem_filter.mp ht
    obtain ⟨ha, hbc_mem⟩ := Finset.mem_product.mp hmem
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc_mem
    by_cases hfab : F b a
    · by_cases hfac : F c a
      · by_cases hfbc : F c b
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, hfab, hfac, hfbc⟩)))
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨(a, (c, b)), Finset.mem_product.mpr ⟨ha, ?_⟩, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, hb⟩, hbc, hfbc⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨((c, a), b), Finset.mem_product.mpr ⟨?_, hb⟩, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, ha⟩, hac, hfac⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨((b, a), c), Finset.mem_product.mpr ⟨?_, hc⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hab, hfab⟩
  have h1 := Finset.card_union_le (triangleTuples A F) (frontLift A B)
  have h2 := Finset.card_union_le (triangleTuples A F ∪ frontLift A B) (outerLift A B)
  have h3 := Finset.card_union_le ((triangleTuples A F ∪ frontLift A B) ∪ outerLift A B)
    (backLift A B)
  have hf : (frontLift A B).card ≤ B.card * A.card := by
    exact (Finset.card_image_le).trans_eq (Finset.card_product B A)
  have ho : (outerLift A B).card ≤ B.card * A.card := by
    exact (Finset.card_image_le).trans_eq (Finset.card_product B A)
  have hb : (backLift A B).card ≤ A.card * B.card := by
    exact (Finset.card_image_le).trans_eq (Finset.card_product A B)
  have hs := Finset.card_le_card hsub
  dsimp [B] at *
  nlinarith

theorem smallPrime_relationDifference_card_real_le (A : Finset ℕ)
    (n P : ℕ) (hA : A ⊆ Finset.Icc 1 n) (hP : 1 ≤ P) :
    ((relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation).card : ℝ) ≤
      (n : ℝ)^2 / P + n := by
  classical
  let Diag := A.image (fun x => (x, x))
  have hsub : relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation ⊆
      largePrimeNoncoprimePairs n P ∪ Diag := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hmem, hsmall, hnot⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hmem
    by_cases hne : x = y
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, hx, by simp [hne]⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hA hx, hA hy⟩, hsmall, ?_⟩
      intro hc
      exact hnot ⟨hne, hc⟩
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le (largePrimeNoncoprimePairs n P) Diag)
  have hdiag : Diag.card ≤ A.card := Finset.card_image_le
  have hAn : A.card ≤ n := by
    simpa using Finset.card_le_card hA
  have hcardR :
      ((relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation).card : ℝ) ≤
        (largePrimeNoncoprimePairs n P).card + (n : ℝ) := by
    exact_mod_cast (show (relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation).card ≤
      (largePrimeNoncoprimePairs n P).card + n by omega)
  have htail := largePrimeNoncoprimePairs_card_real_le n P hP
  linarith

noncomputable def smallPrimeTriangleDensity (A : Finset ℕ) (P n : ℕ) : ℝ :=
  ((triangleTuples A (smallPrimeDisjoint P)).card : ℝ) / (n : ℝ)^3

/-- Direct arithmetic cutoff error, including all repeated-vertex triples.
This is the empirical density before replacing residue frequencies by CRT
product weights. -/
theorem smallPrimeTriangleDensity_le_coprimeDensity_add_tail (A : Finset ℕ)
    (n P : ℕ) (hA : A ⊆ Finset.Icc 1 n) (hn : 0 < n) (hP : 1 ≤ P) :
    smallPrimeTriangleDensity A P n ≤ orderedCoprimeTriangleDensity A n +
      3 / (P : ℝ) + 3 / (n : ℝ) := by
  have hAn : (A.card : ℝ) ≤ n := by
    exact_mod_cast (show A.card ≤ n by simpa using Finset.card_le_card hA)
  have hdiff := smallPrime_relationDifference_card_real_le A n P hA hP
  have htri : ((triangleTuples A (smallPrimeDisjoint P)).card : ℝ) ≤
      (triangleTuples A coprimeRelation).card +
        3 * (A.card : ℝ) * (relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation).card := by
    exact_mod_cast triangleTuples_card_le_of_relationDifference A (smallPrimeDisjoint P) coprimeRelation
  have hmul : (A.card : ℝ) *
      (relationDifferencePairs A (smallPrimeDisjoint P) coprimeRelation).card ≤
        (n : ℝ) * ((n : ℝ)^2 / P + n) := by
    apply mul_le_mul hAn hdiff <;> positivity
  have hraw : ((triangleTuples A (smallPrimeDisjoint P)).card : ℝ) ≤
      (orderedTriangleCount A coprimeRelation : ℝ) +
        3 * ((n : ℝ) * ((n : ℝ)^2 / P + n)) := by
    simp only [triangleTuples_card_eq] at htri ⊢
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  unfold smallPrimeTriangleDensity orderedCoprimeTriangleDensity
  have hh := div_le_div_of_nonneg_right hraw (pow_pos hnR 3).le
  have heq : ((orderedTriangleCount A coprimeRelation : ℝ) +
      3 * ((n : ℝ) * ((n : ℝ)^2 / P + n))) / (n : ℝ)^3 =
        (orderedTriangleCount A coprimeRelation : ℝ) / (n : ℝ)^3 +
          3 / (P : ℝ) + 3 / (n : ℝ) := by
    field_simp
    ring
  rw [heq] at hh
  exact hh

/-- Complete uniform quantifier interface for the empirical finite-cutoff
model. A single cutoff and threshold work for every set in the prefix. -/
theorem smallPrimeTriangleDensity_eventually_small (l : ℕ) (hl : 1 ≤ l)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ P : ℕ, 5 ≤ P ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → ¬ ContainsTripartite A l →
        smallPrimeTriangleDensity A P n < gamma := by
  obtain ⟨P, hPbig⟩ := exists_nat_gt (max (9 / gamma) 5)
  have hP9 : 9 / gamma < (P : ℝ) := (le_max_left _ _).trans_lt hPbig
  have hP5R : (5 : ℝ) < P := (le_max_right _ _).trans_lt hPbig
  have hP5 : 5 ≤ P := by exact_mod_cast hP5R.le
  have hPR : (0 : ℝ) < P := by linarith
  have htail : 3 / (P : ℝ) < gamma / 3 := by
    apply (div_lt_iff₀ hPR).mpr
    have hg := (div_lt_iff₀ hgamma).mp hP9
    nlinarith
  obtain ⟨N, hN⟩ := ordered_coprime_triangle_density_eventually_small l hl
    (show 0 < gamma / 3 by positivity)
  refine ⟨P, hP5, max N P, ?_⟩
  intro n hn A hA hno
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hnP : P ≤ n := (Nat.le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hAn : A.card ≤ n := by simpa using Finset.card_le_card hA
  have htri := hN n hnN A hAn hno
  have herror := smallPrimeTriangleDensity_le_coprimeDensity_add_tail A n P hA hnpos (by omega)
  have hnR : (P : ℝ) ≤ n := by exact_mod_cast hnP
  have hrecip := one_div_le_one_div_of_le hPR hnR
  have hlast : 3 / (n : ℝ) ≤ 3 / (P : ℝ) := by
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 3)
  linarith

#print axioms triangleTuples_card_eq
#print axioms triangleTuples_card_le_of_relationDifference
#print axioms smallPrime_relationDifference_card_real_le
#print axioms smallPrimeTriangleDensity_le_coprimeDensity_add_tail
#print axioms smallPrimeTriangleDensity_eventually_small

end Erdos883Second.Link
