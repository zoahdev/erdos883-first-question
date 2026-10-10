import Erdos883SecondSignatureOutside

namespace Erdos883Second.Signature
noncomputable section
open scoped BigOperators
open Erdos883.SecondSpectral

theorem dense_card_real_lower (n : ℕ) (A : Finset ℕ)
    (hcard : n / 2 + n / 3 - n / 6 < A.card) :
    (2 / 3 : ℝ) * n - 2 ≤ A.card := by
  have hsub : n / 6 ≤ n / 2 + n / 3 := by omega
  have hcardR : ((n / 2 : ℕ) : ℝ) + (n / 3 : ℕ) - (n / 6 : ℕ) < A.card := by
    have hh : ((n / 2 + n / 3 - n / 6 : ℕ) : ℝ) < A.card := by
      exact_mod_cast hcard
    simpa only [Nat.cast_sub hsub, Nat.cast_add] using hh
  have hn2 : (n : ℝ) = 2 * (n / 2 : ℕ) + (n % 2 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n 2).symm
  have hn3 : (n : ℝ) = 3 * (n / 3 : ℕ) + (n % 3 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n 3).symm
  have hn6 : (n : ℝ) = 6 * (n / 6 : ℕ) + (n % 6 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n 6).symm
  have hm2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show n % 2 ≤ 1 by omega)
  have hm3 : ((n % 3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show n % 3 ≤ 2 by omega)
  have hm6 : (0 : ℝ) ≤ (n % 6 : ℕ) := by positivity
  nlinarith

theorem full_occupancy_mean_lower_of_dense (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hcard : n / 2 + n / 3 - n / 6 < A.card) :
    (2 / 3 : ℝ) - (2 + (modulus P : ℝ)) / n ≤
      fullSignatureMean (bigPrimeValue P) (fullOccupancy n P h2 h3 A) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden := dense_card_real_lower n A hcard
  have hratio : (2 / 3 : ℝ) - 2 / n ≤ (A.card : ℝ) / n := by
    have hh := div_le_div_of_nonneg_right hden hnR.le
    have he : ((2 / 3 : ℝ) * n - 2) / n = 2 / 3 - 2 / n := by
      field_simp
    rwa [he] at hh
  have herr := (abs_le.mp (full_occupancy_mean_error n hn P hp hc h2 h3 A hA)).1
  rw [add_div]
  linarith

theorem full_occupancy_outside_lower_of_far (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hc : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (δ : ℝ) (hfar : δ * n ≤ ((A \ Near.standardUniverse n).card : ℝ)) :
    δ ≤ fullOutsideMass (bigPrimeValue P) (fullOccupancy n P h2 h3 A) +
      (modulus P : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : δ ≤ ((A \ Near.standardUniverse n).card : ℝ) / n :=
    (le_div_iff₀ hnR).mpr hfar
  have herr := (abs_le.mp (full_occupancy_outside_error n hn P hp hc h2 h3 A hA)).1
  linarith

#print axioms dense_card_real_lower
#print axioms full_occupancy_mean_lower_of_dense
#print axioms full_occupancy_outside_lower_of_far
end
end Erdos883Second.Signature
