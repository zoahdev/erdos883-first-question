import Erdos883SecondNearConstruction

namespace Erdos883Second.Near
open Erdos883Verified

/-- Natural-number inequalities giving the finite construction a rational
profile `1/s`. These deliberately keep all rounding terms visible. -/
theorem finite_tripartite_of_integer_budgets {n l k r E s C : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 n)
    (hcard : n / 2 + n / 3 - n / 6 < A.card)
    (hs : 1 ≤ s) (hC : momentConstant k = (C : ℚ))
    (hprofile : 4 * C * n < (A \ standardUniverse n).card * s ^ k)
    (hsmall : 48 * (A \ standardUniverse n).card * s ^ (l + 1) ≤ n)
    (hl : 48 * (l + 1) * s ^ (l + 1) ≤ n)
    (hE : 48 * E * s ^ (l + 1) ≤ n)
    (herr : supportConstant r ^ r * n ^ (l + 1) < (E + 1) ^ r) :
    ContainsTripartite A l := by
  let t := (A \ standardUniverse n).card
  let m := (standardUniverse n \ A).card
  let z : ℚ := (s : ℚ)⁻¹
  let W : ℚ := (n : ℚ) / 6 * z ^ (l + 1)
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hz : 0 < z := inv_pos.mpr hsQ
  have hm : (m : ℚ) < t := by exact_mod_cast missing_lt_extra hcard
  have hb : momentConstant k * n * z ^ k < (t : ℚ) / 4 := by
    dsimp [z, t]
    rw [hC, inv_pow, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (pow_pos hsQ k)).mpr
    have hpQ : (4 : ℚ) * C * n < (A \ standardUniverse n).card * (s : ℚ) ^ k := by
      exact_mod_cast hprofile
    nlinarith
  have hWnonneg : 0 ≤ W := by dsimp [W]; positivity
  have htW : (t : ℚ) ≤ W / 8 := by
    dsimp [W, z, t]
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 8)).mpr
    apply (le_div_iff₀ (pow_pos hsQ (l + 1))).mpr
    have hpQ : (48 : ℚ) * (A \ standardUniverse n).card * (s : ℚ) ^ (l + 1) ≤ n := by
      exact_mod_cast hsmall
    nlinarith
  have hlW : (l : ℚ) + 1 ≤ W / 8 := by
    dsimp [W, z]
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 8)).mpr
    apply (le_div_iff₀ (pow_pos hsQ (l + 1))).mpr
    have hpQ : (48 : ℚ) * ((l : ℚ) + 1) * (s : ℚ) ^ (l + 1) ≤ n := by
      exact_mod_cast hl
    nlinarith
  have hEW : (E : ℚ) ≤ W / 8 := by
    dsimp [W, z]
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 8)).mpr
    apply (le_div_iff₀ (pow_pos hsQ (l + 1))).mpr
    have hpQ : (48 : ℚ) * E * (s : ℚ) ^ (l + 1) ≤ n := by
      exact_mod_cast hE
    nlinarith
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hs)
  have hzpow : z ^ (l + 1) ≤ z := by
    rw [pow_succ]
    simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hz.le hz1) hz.le
  have hWL : W ≤ (n : ℚ) / 6 * z :=
    mul_le_mul_of_nonneg_left hzpow (by positivity)
  have hWR : 3 * W = (n : ℚ) / 2 * z ^ (l + 1) := by dsimp [W]; ring
  apply finite_tripartite_of_certificate hA
  exact {
    n_pos := by
      have hp : 0 < n := lt_of_lt_of_le (by positivity : 0 < 48 * (l + 1) * s ^ (l + 1)) hl
      omega
    z_pos := hz
    good_apex := by dsimp [t] at hb; linarith
    support_error := herr
    left_budget := by change (m : ℚ) + _ + l ≤ _; linarith
    right_budget := by change (m : ℚ) + l ≤ _; linarith }

#print axioms finite_tripartite_of_integer_budgets
end Erdos883Second.Near

