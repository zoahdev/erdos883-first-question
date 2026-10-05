import Erdos883LargeNeighbors

namespace Erdos883Verified.Improved

/-- A coarse exponential domination removes logarithms from the large-scale estimate. -/
theorem three_pow_ge_scaled_sq {w : ℕ} (hw : 25 ≤ w) :
    (8000 * w) ^ 2 ≤ 3 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    rw [pow_succ (3 : ℕ)]
    have h : (w + 1) ^ 2 ≤ 3 * w ^ 2 := by nlinarith
    nlinarith

/-- The joint support of two odd integers below `n` has a small linear budget. -/
theorem odd_lcm_primeFactors_scaled_card_le {n u v : ℕ}
    (hn : 200000 ≤ n) (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v) (hun : u ≤ n) (hvn : v ≤ n) :
    8000 * (Nat.lcm u v).primeFactors.card ≤ n := by
  let w := (Nat.lcm u v).primeFactors.card
  by_cases hw : w ≤ 25
  · dsimp [w] at hw ⊢
    omega
  · have hpow : 3 ^ w ≤ n ^ 2 := by
      calc
        _ ≤ Nat.lcm u v := odd_primeFactors_three_pow_le (Nat.lcm_pos hu hv)
          ((huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v))
        _ ≤ u * v := Nat.lcm_le_mul hu hv
        _ ≤ n * n := Nat.mul_le_mul hun hvn
        _ = n ^ 2 := by ring
    have hsq := (three_pow_ge_scaled_sq (by omega : 25 ≤ w)).trans hpow
    nlinarith only [hsq]

end Erdos883Verified.Improved

namespace Erdos883Verified.Improved

/-- The main density contribution alone dominates thirty-one and a half square roots. -/
theorem odd_lcm_density_mul_half_gt {n u v : ℕ}
    (hn : 200000 ≤ n) (hu : 0 < u) (hv : 0 < v)
    (huodd : Odd u) (hvodd : Odd v) (hun : u ≤ n) (hvn : v ≤ n) :
    (63 / 2 : ℝ) * Real.sqrt n <
      ((n / 2 : ℕ) : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) := by
  let r : ℝ := totientDensity (Nat.lcm u v)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact_mod_cast totientDensity_nonneg (Nat.lcm u v)
  have hn' : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < n := by linarith
  have hw : (8000 : ℝ) * (Nat.lcm u v).primeFactors.card ≤ n := by
    exact_mod_cast odd_lcm_primeFactors_scaled_card_le hn hu hv huodd hvodd hun hvn
  have hr : (3 : ℝ) ≤ (4 * (Nat.lcm u v).primeFactors.card + 3) * r ^ 2 := by
    dsimp [r]
    exact_mod_cast odd_totientDensity_wallis (Nat.lcm_pos hu hv)
      ((huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v))
  have hden : (4 : ℝ) * (Nat.lcm u v).primeFactors.card + 3 ≤
      (103 / 200000 : ℝ) * n := by linarith
  have hrn : (600000 / 103 : ℝ) ≤ n * r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hden (sq_nonneg r)
    nlinarith only [hr, hm]
  have hq : (49 : ℝ) / 100 * n ≤ ((n / 2 : ℕ) : ℝ) := by
    have hnat : n ≤ 2 * (n / 2) + 1 := by omega
    have hreal : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  have hsq : (144060 / 103 : ℝ) * n ≤ (((n / 2 : ℕ) : ℝ) * r) ^ 2 := by
    calc
      _ = ((600000 / 103 : ℝ) * n) * ((49 : ℝ) / 100) ^ 2 := by ring
      _ ≤ ((n * r ^ 2) * n) * ((49 : ℝ) / 100) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrn hn0) (by positivity)
      _ = (((49 : ℝ) / 100) * n * r) ^ 2 := by ring
      _ ≤ _ := (sq_le_sq₀ (by positivity) (by positivity)).mpr
        (mul_le_mul_of_nonneg_right hq hr0)
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hn0
  change (63 / 2 : ℝ) * Real.sqrt n < ((n / 2 : ℕ) : ℝ) * r
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  nlinarith only [hsq, hs, hnpos]

/-- Uniform common-even-neighbor bound above two hundred thousand (Part IV.5). -/
theorem rawCommon_coprime_even_card_gt_thirty_sqrt {n u v : ℕ}
    (hn : 200000 ≤ n) (hu : 0 < u) (hv : 0 < v)
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

end Erdos883Verified.Improved

#print axioms Erdos883Verified.Improved.three_pow_ge_scaled_sq
#print axioms Erdos883Verified.Improved.odd_lcm_primeFactors_scaled_card_le
#print axioms Erdos883Verified.Improved.odd_lcm_density_mul_half_gt
#print axioms Erdos883Verified.Improved.rawCommon_coprime_even_card_gt_thirty_sqrt
