import Erdos883TotientMoment

/-!
Independent arbitrary-order finite totient moments for the near-U construction.
The generic finite divisor-weight expansion is imported from the user's already
attributed first-question infrastructure; this is not a second-question proof.
-/

namespace Erdos883Second.Near

open Erdos883Verified

def momentWeight (k p : ℕ) : ℚ :=
  ((p : ℚ) / ((p : ℚ) - 1)) ^ k - 1

def momentExponent (k : ℕ) : ℕ := 2 * (2 ^ k - 1)

def momentConstant (k : ℕ) : ℚ := 2 ^ momentExponent k

theorem momentExponent_cast (k : ℕ) :
    (momentExponent k : ℚ) = 2 * ((2 : ℚ) ^ k - 1) := by
  have h : 1 ≤ (2 : ℕ) ^ k := one_le_pow₀ (by norm_num)
  simp only [momentExponent, Nat.cast_mul, Nat.cast_sub h, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one]

/-- The secant bound on `[0,1]`, proved by induction rather than convexity. -/
theorem one_add_pow_sub_one_le (k : ℕ) {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ k - 1 ≤ ((2 : ℚ) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : (1 + x) ^ k ≤ (2 : ℚ) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    have hm := mul_le_mul_of_nonneg_right hp hx0
    rw [pow_succ, pow_succ]
    nlinarith

theorem momentWeight_nonneg {k p : ℕ} (hp : p.Prime) :
    0 ≤ momentWeight k p := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hratio : (1 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hpq)).mpr
    linarith
  exact sub_nonneg.mpr (one_le_pow₀ hratio)

/-- Each Euler increment is bounded by a fixed integer times `p^-2`. -/
theorem momentWeight_div_le {k p : ℕ} (hp : p.Prime) :
    momentWeight k p / p ≤ (momentExponent k : ℚ) / (p : ℚ) ^ 2 := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < p := by linarith
  have hd : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  let x : ℚ := 1 / ((p : ℚ) - 1)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one₀ hd).mpr
    linarith
  have hr : (p : ℚ) / ((p : ℚ) - 1) = 1 + x := by
    dsimp [x]
    field_simp
    ring
  have hmain := one_add_pow_sub_one_le k hx0 hx1
  have hmul : (2 : ℚ) ^ k - 1 ≥ 0 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hx2 : x ≤ 2 / (p : ℚ) := by
    dsimp [x]
    apply (div_le_div_iff₀ hd hp0).mpr
    linarith
  have hweight : momentWeight k p ≤
      ((2 : ℚ) ^ k - 1) * (2 / (p : ℚ)) := by
    calc
      momentWeight k p = (1 + x) ^ k - 1 := by rw [momentWeight, hr]
      _ ≤ ((2 : ℚ) ^ k - 1) * x := hmain
      _ ≤ _ := mul_le_mul_of_nonneg_left hx2 hmul
  calc
    _ ≤ (((2 : ℚ) ^ k - 1) * (2 / (p : ℚ))) / (p : ℚ) :=
      div_le_div_of_nonneg_right hweight hp0.le
    _ = _ := by rw [momentExponent_cast]; ring

/-- The inverse density has its exact Euler product for every natural order. -/
theorem inv_totientDensity_pow_eq_prod {v : ℕ} (hv : 0 < v) (k : ℕ) :
    (totientDensity v)⁻¹ ^ k =
      ∏ p ∈ v.primeFactors, (1 + momentWeight k p) := by
  rw [totientDensity_eq_prod hv, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors_of_ne_zero hv.ne').mp hp
  have hpq : (1 : ℚ) < p := by exact_mod_cast hprime.1.one_lt
  have hi : (1 - (p : ℚ)⁻¹)⁻¹ = (p : ℚ) / ((p : ℚ) - 1) := by
    field_simp
  rw [hi]
  simp [momentWeight]

/-- Arbitrary finite-order moment, still with its exact finite Euler bound. -/
theorem inverse_totient_moment_le_euler (n k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ v ∈ Finset.Icc 1 n, v.primeFactors ⊆ P) :
    (∑ v ∈ Finset.Icc 1 n, (totientDensity v)⁻¹ ^ k) ≤
      (n : ℚ) * ∏ p ∈ P, (1 + momentWeight k p / p) := by
  calc
    _ = ∑ v ∈ Finset.Icc 1 n,
        ∏ p ∈ P.filter (fun p => p ∣ v), (1 + momentWeight k p) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp hv).1
      rw [prime_filter_eq_primeFactors hvpos P hP (hs v hv),
        inv_totientDensity_pow_eq_prod hvpos k]
    _ ≤ _ := weighted_prime_filter_sum_le n P hP (momentWeight k)
      (fun p hp => momentWeight_nonneg (hP p hp))

#print axioms inverse_totient_moment_le_euler
#print axioms momentWeight_div_le

end Erdos883Second.Near
