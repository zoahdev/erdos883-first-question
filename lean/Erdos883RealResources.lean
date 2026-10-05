import Erdos883NeighborDiscrepancy
import Erdos883UniformDiscrepancy
import Erdos883ThresholdAccounting

namespace Erdos883Verified

/-- Casted common-neighbor discrepancy, strictly below the uniform square-root loss. -/
theorem real_raw_resources_gt_density {n u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (hun : u ≤ n) (hvn : v ≤ n) :
    ((n / 2 : ℕ) : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) -
        (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) ∧
    (n : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) -
        (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (Finset.Icc 1 n) u v).card : ℝ) := by
  have herr := odd_lcm_sharp_error_lt_three_halves_sqrt hu hv huodd hvodd hun hvn
  have heQ := rawCommon_coprime_even_card_ge_density_sub_error n hu hv huodd hvodd
  have hrQ := rawCommon_coprime_Icc_card_ge_density_sub_error n hu hv
  have he : ((n / 2 : ℕ) : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) -
      (coprimeDiscrepancyError (Nat.lcm u v).primeFactors.card : ℝ) ≤
      ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) := by exact_mod_cast heQ
  have hr : (n : ℝ) * (totientDensity (Nat.lcm u v) : ℝ) -
      (coprimeDiscrepancyError (Nat.lcm u v).primeFactors.card : ℝ) ≤
      ((rawCommon Nat.Coprime (Finset.Icc 1 n) u v).card : ℝ) := by exact_mod_cast hrQ
  change (coprimeDiscrepancyError (Nat.lcm u v).primeFactors.card : ℝ) < _ at herr
  constructor <;> linarith

/-- The product-density alternative requires no matching signature. -/
theorem real_unstructured_resources {n u v : ℕ} {t : ℝ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (hun : u ≤ n) (hvn : v ≤ n) (ht : 0 ≤ t)
    (htu : t ≤ (totientDensity u : ℝ)) (htv : t ≤ (totientDensity v : ℝ)) :
    3 * ((n / 6 : ℕ) : ℝ) * t ^ 2 - (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) ∧
    6 * ((n / 6 : ℕ) : ℝ) * t ^ 2 - (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (Finset.Icc 1 n) u v).card : ℝ) := by
  have hproductQ := totientDensity_lcm_ge_mul hu hv
  have hproduct : (totientDensity u : ℝ) * (totientDensity v : ℝ) ≤
      (totientDensity (Nat.lcm u v) : ℝ) := by exact_mod_cast hproductQ
  have hnu : 0 ≤ (totientDensity u : ℝ) := by exact_mod_cast totientDensity_nonneg u
  have hsq : t ^ 2 ≤ (totientDensity (Nat.lcm u v) : ℝ) := by
    have h := mul_le_mul htu htv ht hnu
    nlinarith
  have hq : 3 * ((n / 6 : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast three_m_le_half n
  have hn : 6 * ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 6 * (n / 6) ≤ n by omega)
  have he := mul_le_mul hq hsq (sq_nonneg t) (Nat.cast_nonneg (n / 2))
  have hr := mul_le_mul hn hsq (sq_nonneg t) (Nat.cast_nonneg n)
  have hraw := real_raw_resources_gt_density hu hv huodd hvodd hun hvn
  exact ⟨(sub_le_sub_right he _).trans_lt hraw.1,
    (sub_le_sub_right hr _).trans_lt hraw.2⟩

/-- Matching the full adaptive signature supplies the stronger linear-density alternative. -/
theorem real_structured_resources {n u v : ℕ} {t : ℝ}
    (hn : 1024 < n) (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (hun : u ≤ n) (hvn : v ≤ n) (ht : 0 ≤ t)
    (htu : t ≤ (totientDensity u : ℝ))
    (hcode : divisorSignatureCode (adaptiveTailCoordinates (uniformTailScale n)) u =
      divisorSignatureCode (adaptiveTailCoordinates (uniformTailScale n)) v) :
    (27 / 10 : ℝ) * ((n / 6 : ℕ) : ℝ) * t - (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (evenUniverse n) u v).card : ℝ) ∧
    (27 / 5 : ℝ) * ((n / 6 : ℕ) : ℝ) * t - (3 / 2 : ℝ) * Real.sqrt n <
      ((rawCommon Nat.Coprime (Finset.Icc 1 n) u v).card : ℝ) := by
  have htailQ := totientDensity_lcm_gt_nine_tenths_uniform hn hu hv hvodd hvn hcode
  have htail : (9 / 10 : ℝ) * (totientDensity u : ℝ) <
      (totientDensity (Nat.lcm u v) : ℝ) := by
    have hc : (((9 / 10 : ℚ) * totientDensity u : ℚ) : ℝ) <
        (totientDensity (Nat.lcm u v) : ℝ) := Rat.cast_lt.mpr htailQ
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hc
    exact hc
  have hlo : (9 / 10 : ℝ) * t ≤ (totientDensity (Nat.lcm u v) : ℝ) := by linarith
  have hq : 3 * ((n / 6 : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast three_m_le_half n
  have hn' : 6 * ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 6 * (n / 6) ≤ n by omega)
  have he := mul_le_mul hq hlo (by positivity : 0 ≤ (9 / 10 : ℝ) * t)
    (Nat.cast_nonneg (n / 2))
  have hr := mul_le_mul hn' hlo (by positivity : 0 ≤ (9 / 10 : ℝ) * t)
    (Nat.cast_nonneg n)
  have hraw := real_raw_resources_gt_density hu hv huodd hvodd hun hvn
  constructor <;> nlinarith [hraw.1, hraw.2]

#print axioms real_raw_resources_gt_density
#print axioms real_unstructured_resources
#print axioms real_structured_resources
end Erdos883Verified
