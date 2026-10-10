import Erdos883SecondSignatureFull
import Erdos883SecondNearBase

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators
open Erdos883.SecondSpectral

def selectedCount (P : Finset ℕ) (A : Finset ℕ) (s : Bits P) : ℕ :=
  (A.filter (fun x => signature P x = s)).card

def occupancy (n : ℕ) (P : Finset ℕ) (A : Finset ℕ) (s : Bits P) : ℝ :=
  (selectedCount P A s : ℝ) / prefixCount n P s

def fullOccupancy (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (A : Finset ℕ) (x : FullSignature ↥(bigPrimes P)) : ℝ :=
  occupancy n P A ((signatureEquiv P h2 h3).symm x)

theorem selectedCount_le_prefixCount (n : ℕ) (P : Finset ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (s : Bits P) : selectedCount P A s ≤ prefixCount n P s := by
  rw [prefixCount_card_Icc]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hA)

theorem occupancy_bounds (n : ℕ) (P : Finset ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (s : Bits P) :
    0 ≤ occupancy n P A s ∧ occupancy n P A s ≤ 1 := by
  have hle := selectedCount_le_prefixCount n P A hA s
  unfold occupancy
  constructor
  · positivity
  · by_cases hm : prefixCount n P s = 0
    · simp [hm]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hm)).mpr
      exact_mod_cast hle

theorem fullOccupancy_bounds (n : ℕ) (P : Finset ℕ) (h2 : 2 ∈ P) (h3 : 3 ∈ P)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (x : FullSignature ↥(bigPrimes P)) :
    0 ≤ fullOccupancy n P h2 h3 A x ∧ fullOccupancy n P h2 h3 A x ≤ 1 :=
  occupancy_bounds n P A hA _

theorem occupancy_weight (n : ℕ) (P : Finset ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (s : Bits P) :
    empiricalWeight n P s * occupancy n P A s = (selectedCount P A s : ℝ) / n := by
  have hle := selectedCount_le_prefixCount n P A hA s
  unfold empiricalWeight occupancy
  by_cases hm : prefixCount n P s = 0
  · have hc : selectedCount P A s = 0 := by omega
    simp [hm, hc]
  · have hmR : (prefixCount n P s : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

theorem selectedCount_weighted_sum (P : Finset ℕ) (A : Finset ℕ) (g : Bits P → ℝ) :
    (∑ s : Bits P, (selectedCount P A s : ℝ) * g s) = ∑ x ∈ A, g (signature P x) := by
  have he (s : Bits P) :
      (∑ x ∈ A.filter (fun x => signature P x = s), g (signature P x)) =
        (selectedCount P A s : ℝ) * g s := by
    calc
      _ = ∑ x ∈ A.filter (fun x => signature P x = s), g s := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp [selectedCount]
  simp_rw [← he]
  exact Finset.sum_fiberwise A (signature P) (fun x => g (signature P x))

theorem empirical_occupancy_expectation (n : ℕ) (P : Finset ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (g : Bits P → ℝ) :
    (∑ s : Bits P, empiricalWeight n P s * occupancy n P A s * g s) =
      (∑ x ∈ A, g (signature P x)) / n := by
  simp_rw [occupancy_weight n P A hA]
  simp only [div_eq_mul_inv]
  have he : (∑ s : Bits P, (selectedCount P A s : ℝ) * (n : ℝ)⁻¹ * g s) =
      (∑ s : Bits P, (selectedCount P A s : ℝ) * g s) * (n : ℝ)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he, selectedCount_weighted_sum]

theorem signature_expectation_error (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (f : Bits P → ℝ) (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    |(∑ s : Bits P, productWeight P s * f s) -
      (∑ s : Bits P, empiricalWeight n P s * f s)| ≤ (modulus P : ℝ) / n := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s : Bits P, |productWeight P s * f s - empiricalWeight n P s * f s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Bits P, |empiricalWeight n P s - productWeight P s| := by
      apply Finset.sum_le_sum
      intro s _
      rw [← sub_mul, abs_mul, abs_of_nonneg (hf s).1, abs_sub_comm]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf s).2
    _ ≤ _ := signature_frequency_l1 n hn P hp hc

theorem full_occupancy_mean_error (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    |fullSignatureMean (bigPrimeValue P) (fullOccupancy n P h2 h3 A) -
      (A.card : ℝ) / n| ≤ (modulus P : ℝ) / n := by
  have hmean : fullSignatureMean (bigPrimeValue P) (fullOccupancy n P h2 h3 A) =
      ∑ s : Bits P, productWeight P s * occupancy n P A s := by
    unfold fullSignatureMean
    rw [← (signatureEquiv P h2 h3).sum_comp]
    simp only [full_weight_reindex, fullOccupancy, Equiv.symm_apply_apply]
  rw [hmean]
  have hactual := empirical_occupancy_expectation n P A hA (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at hactual
  rw [← hactual]
  exact signature_expectation_error n hn P hp hc _ (occupancy_bounds n P A hA)

#print axioms occupancy_weight
#print axioms full_occupancy_mean_error
end
end Erdos883Second.Signature
