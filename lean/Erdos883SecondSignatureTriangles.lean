import Erdos883SecondSignatureOccupancy
import Erdos883SecondSpectralDensity
import Erdos883SecondProductError
import Erdos883SecondLinkTailTriangles

/-! Actual integer-signature triangle counts and the finite CRT replacement
error. The frequency and class-occupancy inputs come from the independent
signature modules; no asymptotic model is substituted for the integer count. -/

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators
open Erdos883.SecondSpectral

def cutoffPrimes (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter Nat.Prime

theorem mem_cutoffPrimes (K p : ℕ) : p ∈ cutoffPrimes K ↔ p.Prime ∧ p ≤ K := by
  simp [cutoffPrimes, and_comm]

def bitsDisjoint (P : Finset ℕ) (s t : Bits P) : Prop :=
  ∀ p, ¬ (s p = true ∧ t p = true)

def bitsTriangleAllowed (P : Finset ℕ) (z : Bits P × Bits P × Bits P) : Prop :=
  bitsDisjoint P z.1 z.2.1 ∧ bitsDisjoint P z.1 z.2.2 ∧ bitsDisjoint P z.2.1 z.2.2

instance (P : Finset ℕ) : DecidableRel (bitsDisjoint P) :=
  fun s t => by unfold bitsDisjoint; infer_instance

instance (P : Finset ℕ) : DecidablePred (bitsTriangleAllowed P) :=
  fun z => by unfold bitsTriangleAllowed; infer_instance

theorem full_disjoint_reindex (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (s t : Bits P) :
    fullSignatureDisjoint (signatureEquiv P h2 h3 s) (signatureEquiv P h2 h3 t) ↔
      bitsDisjoint P s t := by
  simp only [fullSignatureDisjoint, signatureEquiv, Equiv.coe_fn_mk, bitsDisjoint]
  constructor
  · rintro ⟨h2st, h3st, hbig⟩ p
    by_cases hp2 : (p : ℕ) = 2
    · have he : p = ⟨2, h2⟩ := Subtype.ext hp2
      simpa only [he] using h2st
    · by_cases hp3 : (p : ℕ) = 3
      · have he : p = ⟨3, h3⟩ := Subtype.ext hp3
        simpa only [he] using h3st
      · exact hbig ⟨p, by simp [bigPrimes, hp2, hp3, p.property]⟩
  · intro h
    exact ⟨h ⟨2, h2⟩, h ⟨3, h3⟩, fun p => h ⟨p, bigPrimes_subset P p.property⟩⟩

theorem bits_disjoint_signature_cutoff (K x y : ℕ) :
    bitsDisjoint (cutoffPrimes K) (signature (cutoffPrimes K) x)
      (signature (cutoffPrimes K) y) ↔ Link.smallPrimeDisjoint K x y := by
  simp only [bitsDisjoint, signature, decide_eq_true_eq, Link.smallPrimeDisjoint]
  constructor
  · intro h p hp hpK
    exact h ⟨p, (mem_cutoffPrimes K p).mpr ⟨hp, hpK⟩⟩
  · intro h p
    have hp := (mem_cutoffPrimes K p).mp p.property
    exact h p hp.1 hp.2

theorem bitsDisjoint_symm (P : Finset ℕ) (s t : Bits P) :
    bitsDisjoint P s t ↔ bitsDisjoint P t s := by
  simp only [bitsDisjoint, and_comm]

theorem selectedCount_triple_weighted_sum (P : Finset ℕ) (A : Finset ℕ)
    (g : Bits P → Bits P → Bits P → ℝ) :
    (∑ s : Bits P, (selectedCount P A s : ℝ) *
      (∑ t : Bits P, (selectedCount P A t : ℝ) *
        (∑ u : Bits P, (selectedCount P A u : ℝ) * g s t u))) =
      ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
        g (signature P x) (signature P y) (signature P z) := by
  simp_rw [selectedCount_weighted_sum]

def empiricalFullTriangleDensity (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P)
    (h3 : 3 ∈ P) (A : Finset ℕ) : ℝ :=
  ∑ z : FullSignatureTriple ↥(bigPrimes P), if fullTriangleAllowed z then
    (fullEmpiricalWeight n P h2 h3 z.1 * fullEmpiricalWeight n P h2 h3 z.2.1 *
      fullEmpiricalWeight n P h2 h3 z.2.2) *
        (fullOccupancy n P h2 h3 A z.1 * fullOccupancy n P h2 h3 A z.2.1 *
          fullOccupancy n P h2 h3 A z.2.2) else 0

theorem empiricalFullTriangleDensity_counts (n : ℕ) (P : Finset ℕ)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    empiricalFullTriangleDensity n P h2 h3 A =
      (∑ z : Bits P × Bits P × Bits P, if bitsTriangleAllowed P z then
        (selectedCount P A z.1 : ℝ) * selectedCount P A z.2.1 *
          selectedCount P A z.2.2 else 0) / (n : ℝ)^3 := by
  classical
  let e := signatureEquiv P h2 h3
  have hreindex : empiricalFullTriangleDensity n P h2 h3 A =
      ∑ z : Bits P × Bits P × Bits P, if bitsTriangleAllowed P z then
        (empiricalWeight n P z.1 * empiricalWeight n P z.2.1 * empiricalWeight n P z.2.2) *
          (occupancy n P A z.1 * occupancy n P A z.2.1 * occupancy n P A z.2.2) else 0 := by
    unfold empiricalFullTriangleDensity
    apply (Fintype.sum_equiv (e.prodCongr (e.prodCongr e)) _ _ _).symm
    rintro ⟨s, t, u⟩
    simp only [Equiv.prodCongr_apply, Prod.map, fullTriangleAllowed, full_disjoint_reindex,
      fullEmpiricalWeight, fullOccupancy, Equiv.symm_apply_apply, bitsTriangleAllowed, e]
  rw [hreindex, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : bitsTriangleAllowed P z
  · simp only [if_pos hz]
    calc
      _ = (empiricalWeight n P z.1 * occupancy n P A z.1) *
          (empiricalWeight n P z.2.1 * occupancy n P A z.2.1) *
          (empiricalWeight n P z.2.2 * occupancy n P A z.2.2) := by ring
      _ = _ := by simp only [occupancy_weight n P A hA]; ring
  · simp [hz]

theorem signature_triangle_count_cutoff (K : ℕ) (A : Finset ℕ) :
    (∑ z : Bits (cutoffPrimes K) × Bits (cutoffPrimes K) × Bits (cutoffPrimes K),
      if bitsTriangleAllowed (cutoffPrimes K) z then
        (selectedCount (cutoffPrimes K) A z.1 : ℝ) * selectedCount (cutoffPrimes K) A z.2.1 *
          selectedCount (cutoffPrimes K) A z.2.2 else 0) =
      ((Link.triangleTuples A (Link.smallPrimeDisjoint K)).card : ℝ) := by
  classical
  let P := cutoffPrimes K
  have hcount := selectedCount_triple_weighted_sum P A
    (fun s t u => if bitsTriangleAllowed P (s, t, u) then 1 else 0)
  have heq : (∑ z : Bits P × Bits P × Bits P, if bitsTriangleAllowed P z then
      (selectedCount P A z.1 : ℝ) * selectedCount P A z.2.1 * selectedCount P A z.2.2 else 0) =
      ∑ s : Bits P, (selectedCount P A s : ℝ) *
        (∑ t : Bits P, (selectedCount P A t : ℝ) *
          (∑ u : Bits P, (selectedCount P A u : ℝ) *
            (if bitsTriangleAllowed P (s, t, u) then 1 else 0))) := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> ring
  change (∑ z : Bits P × Bits P × Bits P, _) = _
  rw [heq, hcount]
  simp only [Link.triangleTuples, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  simp only [bitsTriangleAllowed, P, bits_disjoint_signature_cutoff]
  simp only [Link.smallPrimeDisjoint, and_comm]

theorem empiricalFullTriangleDensity_eq_actual (n K : ℕ)
    (h2 : 2 ∈ cutoffPrimes K) (h3 : 3 ∈ cutoffPrimes K)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    empiricalFullTriangleDensity n (cutoffPrimes K) h2 h3 A =
      Link.smallPrimeTriangleDensity A K n := by
  rw [empiricalFullTriangleDensity_counts n (cutoffPrimes K) h2 h3 A hA,
    signature_triangle_count_cutoff]
  rfl

theorem full_triangle_density_error (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    |fullTriangleDensity (bigPrimeValue P) (fullOccupancy n P h2 h3 A) -
      empiricalFullTriangleDensity n P h2 h3 A| ≤ 3 * (modulus P : ℝ) / n := by
  classical
  let f := fullOccupancy n P h2 h3 A
  let g : FullSignatureTriple ↥(bigPrimes P) → ℝ := fun z =>
    if fullTriangleAllowed z then f z.1 * f z.2.1 * f z.2.2 else 0
  have hf := fullOccupancy_bounds n P h2 h3 A hA
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    dsimp [g]
    split_ifs
    · exact mul_nonneg (mul_nonneg (hf _).1 (hf _).1) (hf _).1
    · exact le_rfl
  have hg1 : ∀ z, g z ≤ 1 := by
    intro z
    dsimp [g]
    split_ifs
    · exact mul_le_one₀ (mul_le_one₀ (hf _).2 (hf _).1 (hf _).2) (hf _).1 (hf _).2
    · norm_num
  have he := Far.triple_expectation_error
    (fullSignatureWeight (bigPrimeValue P)) (fullEmpiricalWeight n P h2 h3) g
    (fullProductWeight_nonneg P hp hc h2 h3) (fullEmpiricalWeight_nonneg n P h2 h3)
    (fullProductWeight_sum P hp hc h2 h3) (fullEmpiricalWeight_sum n hn P h2 h3) hg0 hg1
  have hfreq := full_signature_frequency_l1 n hn P hp hc h2 h3
  have hfreq' : (∑ x : FullSignature ↥(bigPrimes P),
      |fullSignatureWeight (bigPrimeValue P) x - fullEmpiricalWeight n P h2 h3 x|) ≤
        (modulus P : ℝ) / n := by
    simpa only [abs_sub_comm] using hfreq
  have hbound := he.trans (mul_le_mul_of_nonneg_left hfreq' (by norm_num : (0 : ℝ) ≤ 3))
  simpa only [g, f, Far.tripleWeight, mul_ite, mul_zero, ← mul_div_assoc,
    fullTriangleDensity, empiricalFullTriangleDensity] using hbound

theorem full_triangle_density_le_actual (n K : ℕ) (hn : 0 < n)
    (h2 : 2 ∈ cutoffPrimes K) (h3 : 3 ∈ cutoffPrimes K)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    fullTriangleDensity (bigPrimeValue (cutoffPrimes K))
      (fullOccupancy n (cutoffPrimes K) h2 h3 A) ≤
        Link.smallPrimeTriangleDensity A K n + 3 * (modulus (cutoffPrimes K) : ℝ) / n := by
  have hp : ∀ p ∈ cutoffPrimes K, p.Prime := by
    intro p hp
    exact ((mem_cutoffPrimes K p).mp hp).1
  have he := full_triangle_density_error n hn (cutoffPrimes K)
    (fun p h => (hp p h).pos) (primes_pairwise_coprime _ hp) h2 h3 A hA
  rw [empiricalFullTriangleDensity_eq_actual n K h2 h3 A hA] at he
  have hh := (le_abs_self _).trans he
  linarith

#print axioms empiricalFullTriangleDensity_eq_actual
#print axioms full_triangle_density_error
#print axioms full_triangle_density_le_actual

end
end Erdos883Second.Signature
