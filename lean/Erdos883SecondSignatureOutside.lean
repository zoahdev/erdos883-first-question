import Erdos883SecondSignatureOccupancy

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators
open Erdos883.SecondSpectral

def outsideBit (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P) (s : Bits P) : ℝ :=
  if s ⟨2, h2⟩ = false ∧ s ⟨3, h3⟩ = false then 1 else 0

theorem outsideBit_sum (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    (∑ x ∈ A, outsideBit P h2 h3 (signature P x)) =
      ((A \ Near.standardUniverse n).card : ℝ) := by
  have he : A.filter (fun x => ¬2 ∣ x ∧ ¬3 ∣ x) = A \ Near.standardUniverse n := by
    ext x
    by_cases hx : x ∈ A
    · have hxI := hA hx
      simp [Near.standardUniverse, hx, hxI]
    · simp [hx]
  rw [← he, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp [outsideBit, signature]

theorem full_occupancy_outside_error (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    |fullOutsideMass (bigPrimeValue P) (fullOccupancy n P h2 h3 A) -
      ((A \ Near.standardUniverse n).card : ℝ) / n| ≤ (modulus P : ℝ) / n := by
  have hmodel : fullOutsideMass (bigPrimeValue P) (fullOccupancy n P h2 h3 A) =
      ∑ s : Bits P, productWeight P s * occupancy n P A s * outsideBit P h2 h3 s := by
    unfold fullOutsideMass
    rw [← (signatureEquiv P h2 h3).sum_comp]
    simp only [full_weight_reindex, fullOccupancy, Equiv.symm_apply_apply]
    rfl
  rw [hmodel]
  have hactual := empirical_occupancy_expectation n P A hA (outsideBit P h2 h3)
  rw [outsideBit_sum n P h2 h3 A hA] at hactual
  rw [← hactual]
  have hf (s : Bits P) :
      0 ≤ occupancy n P A s * outsideBit P h2 h3 s ∧
        occupancy n P A s * outsideBit P h2 h3 s ≤ 1 := by
    have hs := occupancy_bounds n P A hA s
    unfold outsideBit
    split <;> simp only [mul_one, mul_zero]
    · exact hs
    · constructor <;> norm_num
  simpa only [mul_assoc] using
    signature_expectation_error n hn P hp hc
      (fun s => occupancy n P A s * outsideBit P h2 h3 s) hf

#print axioms outsideBit_sum
#print axioms full_occupancy_outside_error
end
end Erdos883Second.Signature
