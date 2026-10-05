import Erdos883SharpTail
import Erdos883NeighborDiscrepancy
import Erdos883UniformDiscrepancy

namespace Erdos883Verified

open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The first `w` odd integers greater than one form a universal Euler benchmark. -/
def oddIntegerBenchmark (w : ℕ) : Finset ℕ :=
  (Finset.range w).image (fun i => 2 * i + 3)

/-- A finite Wallis-type lower bound, in division-free form. -/
theorem oddIntegerBenchmark_wallis (w : ℕ) :
    (3 : ℚ) ≤ (4 * w + 3) *
      (∏ i ∈ Finset.range w, (1 - ((2 * i + 3 : ℕ) : ℚ)⁻¹)) ^ 2 := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    rw [Finset.prod_range_succ]
    push_cast
    have hw : (0 : ℚ) ≤ w := Nat.cast_nonneg w
    have hd : (2 * (w : ℚ) + 3) ≠ 0 := by positivity
    have hf : (4 * (w : ℚ) + 3) ≤
        (4 * (w + 1) + 3) * (1 - (2 * (w : ℚ) + 3)⁻¹) ^ 2 := by
      field_simp
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hf
      (sq_nonneg (∏ i ∈ Finset.range w, (1 - ((2 * i + 3 : ℕ) : ℚ)⁻¹)))
    push_cast at ih hm
    nlinarith [ih]

/-- Every odd modulus has the Wallis lower bound for its totient density. -/
theorem odd_totientDensity_wallis {D : ℕ} (hD : 0 < D) (hodd : Odd D) :
    (3 : ℚ) ≤ (4 * D.primeFactors.card + 3) * totientDensity D ^ 2 := by
  let w := D.primeFactors.card
  have hinj : Function.Injective (fun i : ℕ => 2 * i + 3) := by
    intro a b h
    dsimp at h
    omega
  have hcard : (oddIntegerBenchmark w).card = w := by
    rw [oddIntegerBenchmark, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hQ : ∀ p ∈ oddIntegerBenchmark w, 2 ≤ p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    omega
  have hc := finset_euler_product_comparison D.primeFactors (oddIntegerBenchmark w)
    (q := 2 * w + 3) (by omega)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le) hQ
    (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have := Finset.mem_range.mp hi
      omega)
    (by
      intro p hp hn
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpodd := Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      by_contra h
      apply hn
      apply Finset.mem_image.mpr
      refine ⟨(p - 3) / 2, Finset.mem_range.mpr ?_, ?_⟩ <;> omega)
    (by rw [hcard])
  rw [← totientDensity_eq_prod hD] at hc
  have heq : (∏ p ∈ oddIntegerBenchmark w, (1 - (p : ℚ)⁻¹)) =
      ∏ i ∈ Finset.range w, (1 - ((2 * i + 3 : ℕ) : ℚ)⁻¹) := by
    rw [oddIntegerBenchmark, Finset.prod_image]
    exact fun _ _ _ _ h => hinj h
  rw [heq] at hc
  have hnonneg : (0 : ℚ) ≤ ∏ i ∈ Finset.range w,
      (1 - ((2 * i + 3 : ℕ) : ℚ)⁻¹) :=
    Finset.prod_nonneg (fun i _ => eulerFactor_nonneg (by omega))
  have hsq : (∏ i ∈ Finset.range w, (1 - ((2 * i + 3 : ℕ) : ℚ)⁻¹)) ^ 2 ≤
      totientDensity D ^ 2 := sq_le_sq₀ hnonneg (totientDensity_nonneg D) |>.mpr hc
  exact (oddIntegerBenchmark_wallis w).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- Three to the number of distinct prime factors is bounded by any positive odd modulus. -/
theorem odd_primeFactors_three_pow_le {D : ℕ} (hD : 0 < D) (hodd : Odd D) :
    3 ^ D.primeFactors.card ≤ D := by
  calc
    _ = ∏ _p ∈ D.primeFactors, (3 : ℕ) := by simp
    _ ≤ ∏ p ∈ D.primeFactors, p := by
      apply Finset.prod_le_prod (by omega)
      intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpo := Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      omega
    _ ≤ D := Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)

/-- A coarse exponential domination removes logarithms from the large-scale estimate. -/
theorem three_pow_ge_scaled_sq {w : ℕ} (hw : 50 ≤ w) :
    (40000 * w) ^ 2 ≤ 3 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    rw [pow_succ (3 : ℕ)]
    have h : (w + 1) ^ 2 ≤ 3 * w ^ 2 := by nlinarith
    nlinarith

/-- The joint support of two odd integers below `n` has a small linear budget. -/
theorem odd_lcm_primeFactors_scaled_card_le {n u v : ℕ}
    (hn : 2000000 ≤ n) (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v) (hun : u ≤ n) (hvn : v ≤ n) :
    40000 * (Nat.lcm u v).primeFactors.card ≤ n := by
  let w := (Nat.lcm u v).primeFactors.card
  by_cases hw : w ≤ 50
  · dsimp [w] at hw ⊢
    omega
  · have hpow : 3 ^ w ≤ n ^ 2 := by
      calc
        _ ≤ Nat.lcm u v := odd_primeFactors_three_pow_le (Nat.lcm_pos hu hv)
          ((huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v))
        _ ≤ u * v := Nat.lcm_le_mul hu hv
        _ ≤ n * n := Nat.mul_le_mul hun hvn
        _ = n ^ 2 := by ring
    have hsq := (three_pow_ge_scaled_sq (by omega : 50 ≤ w)).trans hpow
    nlinarith only [hsq]

end Erdos883Verified

namespace Erdos883Verified

/-- The main density contribution alone dominates thirty-one and a half square roots. -/
theorem odd_lcm_density_mul_half_gt {n u v : ℕ}
    (hn : 2000000 ≤ n) (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v) (hun : u ≤ n) (hvn : v ≤ n) :
    (63 / 2 : ℝ) * Real.sqrt n <
      ((n / 2 : ℕ) : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) := by
  let r : ℝ := totientDensity (Nat.lcm u v)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact_mod_cast totientDensity_nonneg (Nat.lcm u v)
  have hn' : (2000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < n := by linarith
  have hw : (40000 : ℝ) * (Nat.lcm u v).primeFactors.card ≤ n := by
    exact_mod_cast odd_lcm_primeFactors_scaled_card_le hn hu hv huodd hvodd hun hvn
  have hr : (3 : ℝ) ≤ (4 * (Nat.lcm u v).primeFactors.card + 3) * r ^ 2 := by
    dsimp [r]
    exact_mod_cast odd_totientDensity_wallis (Nat.lcm_pos hu hv)
      ((huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v))
  have hden : (4 : ℝ) * (Nat.lcm u v).primeFactors.card + 3 ≤
      (203 / 2000000 : ℝ) * n := by linarith
  have hrn : (6000000 / 203 : ℝ) ≤ n * r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hden (sq_nonneg r)
    nlinarith only [hr, hm]
  have hq : (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) := by
    have hnat : n ≤ 3 * (n / 2) := by omega
    have hreal : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hsq : (2000000 / 609 : ℝ) * n ≤ (((n / 2 : ℕ) : ℝ) * r) ^ 2 := by
    calc
      _ = ((6000000 / 203 : ℝ) * n) / 9 := by ring
      _ ≤ ((n * r ^ 2) * n) / 9 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrn hn0) (by norm_num)
      _ = ((n : ℝ) / 3 * r) ^ 2 := by ring
      _ ≤ _ := (sq_le_sq₀ (by positivity) (by positivity)).mpr
        (mul_le_mul_of_nonneg_right hq hr0)
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hn0
  change (63 / 2 : ℝ) * Real.sqrt n < ((n / 2 : ℕ) : ℝ) * r
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  nlinarith only [hsq, hs, hnpos]

/-- Uniform common-even-neighbor bound above two million (Part IV.5). -/
theorem rawCommon_coprime_even_card_gt_thirty_sqrt {n u v : ℕ}
    (hn : 2000000 ≤ n) (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v) (hun : u ≤ n) (hvn : v ≤ n) :
    (30 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) := by
  have hmain := odd_lcm_density_mul_half_gt hn hu hv huodd hvodd hun hvn
  have herr := odd_lcm_sharp_error_lt_three_halves_sqrt hu hv huodd hvodd hun hvn
  have hc := (Rat.cast_le (K := ℝ)).mpr
    (rawCommon_coprime_even_card_ge_density_sub_error n hu hv huodd hvodd)
  push_cast at hc
  dsimp [coprimeDiscrepancyError] at hc
  linarith

end Erdos883Verified

#print axioms Erdos883Verified.oddIntegerBenchmark_wallis
#print axioms Erdos883Verified.odd_totientDensity_wallis
#print axioms Erdos883Verified.odd_primeFactors_three_pow_le
#print axioms Erdos883Verified.three_pow_ge_scaled_sq
#print axioms Erdos883Verified.odd_lcm_primeFactors_scaled_card_le
#print axioms Erdos883Verified.odd_lcm_density_mul_half_gt
#print axioms Erdos883Verified.rawCommon_coprime_even_card_gt_thirty_sqrt
