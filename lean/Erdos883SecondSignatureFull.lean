import Erdos883SecondSignatureFrequency
import Erdos883SecondSpectralFull

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators
open Erdos883.SecondSpectral

def bigPrimes (P : Finset ℕ) : Finset ℕ := (P.erase 2).erase 3

theorem bigPrimes_subset (P : Finset ℕ) : bigPrimes P ⊆ P :=
  (Finset.erase_subset 3 (P.erase 2)).trans (Finset.erase_subset 2 P)

def bigPrimeValue (P : Finset ℕ) (p : ↥(bigPrimes P)) : ℕ := p

def signatureEquiv (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P) :
    Bits P ≃ FullSignature ↥(bigPrimes P) where
  toFun s := (s ⟨2, h2⟩, s ⟨3, h3⟩,
    fun p => s ⟨p, bigPrimes_subset P p.property⟩)
  invFun x p := if hp2 : (p : ℕ) = 2 then x.1 else
    if hp3 : (p : ℕ) = 3 then x.2.1 else
      x.2.2 ⟨p, by simp [bigPrimes, hp2, hp3, p.property]⟩
  left_inv s := by
    funext p
    by_cases hp2 : (p : ℕ) = 2
    · have he : p = ⟨2, h2⟩ := Subtype.ext hp2
      subst p
      simp
    · by_cases hp3 : (p : ℕ) = 3
      · have he : p = ⟨3, h3⟩ := Subtype.ext hp3
        subst p
        simp [hp2]
      · simp [hp2, hp3]
  right_inv x := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext p
        have hp2 : (p : ℕ) ≠ 2 := (Finset.mem_erase.mp
          (Finset.mem_erase.mp p.property).2).1
        have hp3 : (p : ℕ) ≠ 3 := (Finset.mem_erase.mp p.property).1
        simp [hp2, hp3]

def extendedCoordinate (P : Finset ℕ) (s : Bits P) (p : ℕ) : ℝ :=
  if hp : p ∈ P then coordinateWeight p (s ⟨p, hp⟩) else 1

theorem productWeight_eq_finset (P : Finset ℕ) (s : Bits P) :
    productWeight P s = ∏ p ∈ P, extendedCoordinate P s p := by
  calc
    _ = ∏ p : ↥P, extendedCoordinate P s p := by
      unfold productWeight tensorWeight
      apply Finset.prod_congr rfl
      intro p _
      simp only [extendedCoordinate, dif_pos p.property]
    _ = _ := Finset.prod_coe_sort P (extendedCoordinate P s)

theorem productWeight_big_restrict (P : Finset ℕ) (s : Bits P) :
    (∏ p ∈ bigPrimes P, extendedCoordinate P s p) =
      productWeight (bigPrimes P) (fun p => s ⟨p, bigPrimes_subset P p.property⟩) := by
  rw [← Finset.prod_coe_sort]
  unfold productWeight tensorWeight
  apply Finset.prod_congr rfl
  intro p _
  simp only [extendedCoordinate, dif_pos (bigPrimes_subset P p.property)]

theorem full_weight_reindex (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (s : Bits P) :
    fullSignatureWeight (bigPrimeValue P) (signatureEquiv P h2 h3 s) = productWeight P s := by
  have h3e : 3 ∈ P.erase 2 := by simp [h3]
  have hbig := productWeight_big_restrict P s
  rw [productWeight_eq_finset P s, ← Finset.mul_prod_erase P _ h2,
    ← Finset.mul_prod_erase (P.erase 2) _ h3e]
  change fullSignatureWeight (bigPrimeValue P) (signatureEquiv P h2 h3 s) =
    extendedCoordinate P s 2 * (extendedCoordinate P s 3 *
      ∏ p ∈ bigPrimes P, extendedCoordinate P s p)
  rw [hbig]
  change coordinateWeight 2 (s ⟨2, h2⟩) * coordinateWeight 3 (s ⟨3, h3⟩) *
      productWeight (bigPrimes P) (fun p => s ⟨p, bigPrimes_subset P p.property⟩) = _
  simp only [extendedCoordinate, dif_pos h2, dif_pos h3, mul_assoc, Nat.cast_ofNat]

def fullEmpiricalWeight (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (x : FullSignature ↥(bigPrimes P)) : ℝ :=
  empiricalWeight n P ((signatureEquiv P h2 h3).symm x)

theorem full_signature_frequency_l1 (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) :
    (∑ x : FullSignature ↥(bigPrimes P),
      |fullEmpiricalWeight n P h2 h3 x - fullSignatureWeight (bigPrimeValue P) x|) ≤
      (modulus P : ℝ) / n := by
  let e := signatureEquiv P h2 h3
  have he : (∑ x : FullSignature ↥(bigPrimes P),
      |fullEmpiricalWeight n P h2 h3 x - fullSignatureWeight (bigPrimeValue P) x|) =
      ∑ s : Bits P, |empiricalWeight n P s - productWeight P s| := by
    rw [← e.sum_comp]
    simp only [fullEmpiricalWeight, e, Equiv.symm_apply_apply, full_weight_reindex]
  rw [he]
  exact signature_frequency_l1 n hn P hp hc

theorem bigPrimeValue_ge_five (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (p : ↥(bigPrimes P)) : 5 ≤ bigPrimeValue P p := by
  exact (hp p (bigPrimes_subset P p.property)).five_le_of_ne_two_of_ne_three
    (Finset.mem_erase.mp (Finset.mem_erase.mp p.property).2).1
    (Finset.mem_erase.mp p.property).1

theorem bigPrimeValue_injective (P : Finset ℕ) : Function.Injective (bigPrimeValue P) := by
  intro p q h
  exact Subtype.ext h

theorem bigPrimeValue_prime (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (p : ↥(bigPrimes P)) : (bigPrimeValue P p).Prime :=
  hp p (bigPrimes_subset P p.property)

theorem fullEmpiricalWeight_nonneg (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (x : FullSignature ↥(bigPrimes P)) : 0 ≤ fullEmpiricalWeight n P h2 h3 x :=
  empiricalWeight_nonneg n P _

theorem fullEmpiricalWeight_sum (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) :
    (∑ x : FullSignature ↥(bigPrimes P), fullEmpiricalWeight n P h2 h3 x) = 1 := by
  exact ((signatureEquiv P h2 h3).symm.sum_comp (empiricalWeight n P)).trans
    (empiricalWeight_sum n hn P)

theorem fullProductWeight_nonneg (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (x : FullSignature ↥(bigPrimes P)) :
    0 ≤ fullSignatureWeight (bigPrimeValue P) x := by
  have he := full_weight_reindex P h2 h3 ((signatureEquiv P h2 h3).symm x)
  rw [Equiv.apply_symm_apply] at he
  rw [he]
  exact productWeight_nonneg P hp hc _

theorem fullProductWeight_sum (P : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime) (h2 : 2 ∈ P) (h3 : 3 ∈ P) :
    (∑ x : FullSignature ↥(bigPrimes P), fullSignatureWeight (bigPrimeValue P) x) = 1 := by
  rw [← (signatureEquiv P h2 h3).sum_comp]
  simp only [full_weight_reindex]
  exact productWeight_sum P hp hc

#print axioms signatureEquiv
#print axioms full_weight_reindex
#print axioms full_signature_frequency_l1
end
end Erdos883Second.Signature
