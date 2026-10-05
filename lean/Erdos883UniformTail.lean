import Erdos883TailDensity
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos883Verified

/-- A natural-number power comparison controls the number of large prime factors. -/
theorem ten_mul_lt_of_pow_le_four_pow {s p a : ℕ}
    (hs : 511 ≤ s) (hp : 2 * s + 3 ≤ p) (hpow : p ^ a ≤ 4 ^ s) :
    10 * a < p := by
  by_contra h
  have hp1024 : 2 ^ 10 ≤ p := by norm_num; omega
  have htwo : 2 * s < 10 * a := by omega
  have hlt : (4 : ℕ) ^ s < p ^ a := by
    calc
      (4 : ℕ) ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
      _ < 2 ^ (10 * a) := Nat.pow_lt_pow_right (by decide) htwo
      _ = (2 ^ 10) ^ a := by rw [pow_mul]
      _ ≤ p ^ a := Nat.pow_le_pow_left hp1024 a
  omega

/-- Bernoulli's inequality in the exact rational form used by the tail bound. -/
theorem thresholdFactor_pow_ge_one_sub_ratio {p a : ℕ} (hp : 2 ≤ p) :
    1 - (a : ℚ) / p ≤ (((p : ℚ) - 1) / p) ^ a := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have h := one_add_mul_sub_le_pow
    (show (-1 : ℚ) ≤ ((p : ℚ) - 1) / p by
      exact le_trans (by norm_num) (thresholdFactor_mem_unitInterval hp).1) a
  have heq : 1 - (a : ℚ) / p = 1 + (a : ℚ) * (((p : ℚ) - 1) / p - 1) := by
    field_simp
    ring
  rw [heq]
  exact h

/-- Fewer than `p/10` Euler factors at threshold `p` lose less than one tenth. -/
theorem thresholdFactor_pow_gt_nine_tenths {p a : ℕ}
    (hp : 2 ≤ p) (ha : 10 * a < p) :
    (9 / 10 : ℚ) < (((p : ℚ) - 1) / p) ^ a := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have ha' : (10 : ℚ) * a < p := by exact_mod_cast ha
  have hratio : (a : ℚ) / p < 1 / 10 := by
    apply (div_lt_iff₀ hp0).mpr
    linarith
  exact lt_of_lt_of_le (by linarith) (thresholdFactor_pow_ge_one_sub_ratio hp)

/-- The universal large-scale threshold estimate, without logarithmic analysis. -/
theorem thresholdFactor_pow_gt_nine_tenths_of_large_scale {s p a : ℕ}
    (hs : 511 ≤ s) (hp : 2 * s + 3 ≤ p) (hpow : p ^ a ≤ 4 ^ s) :
    (9 / 10 : ℚ) < (((p : ℚ) - 1) / p) ^ a := by
  exact thresholdFactor_pow_gt_nine_tenths (by omega)
    (ten_mul_lt_of_pow_le_four_pow hs hp hpow)


/-- The elementary list of `s` odd coordinates beginning at three. -/
def oddTailCoordinates (s : ℕ) : List ℕ :=
  (List.range s).map (fun i => 2 * i + 3)

@[simp] theorem oddTailCoordinates_length (s : ℕ) :
    (oddTailCoordinates s).length = s := by
  simp [oddTailCoordinates]

/-- These coordinates include every odd prime below `2s+3`. -/
theorem oddTailCoordinates_covers {q s : ℕ}
    (hq : q.Prime) (hodd : Odd q) (hqs : q < 2 * s + 3) :
    q ∈ oddTailCoordinates s := by
  have hq2 := hq.two_le
  have hmod := Nat.odd_iff.mp hodd
  have hdiv := Nat.mod_add_div q 2
  apply List.mem_map.mpr
  refine ⟨q / 2 - 1, List.mem_range.mpr (by omega), ?_⟩
  omega

/-- For an odd second endpoint, the signatures need only cover odd primes. -/
theorem missingPrime_ge_of_odd_signature_eq {u v p : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hvodd : Odd v)
    (hcover : ∀ q, q.Prime → Odd q → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v) :
    ∀ q ∈ v.primeFactors \ u.primeFactors, p ≤ q := by
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqv, hqu⟩
  by_contra hqp
  have hmem : q ∈ ps := hcover q (Nat.prime_of_mem_primeFactors hqv)
    (hvodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hqv)) (by omega)
  have hqu' : q ∣ u := (divisorSignatureCode_eq_imp_dvd_iff ps u v hcode hmem).mpr
    (Nat.dvd_of_mem_primeFactors hqv)
  exact hqu ((Nat.mem_primeFactors_of_ne_zero hu.ne').mpr
    ⟨Nat.prime_of_mem_primeFactors hqv, hqu'⟩)

/-- A direct power bound for the number of large distinct prime divisors. -/
theorem primeFactors_subset_pow_card_le {v U p : ℕ} {t : Finset ℕ}
    (hv : 0 < v) (hvU : v ≤ U)
    (ht : t ⊆ v.primeFactors) (hsmall : ∀ q ∈ t, p ≤ q) :
    p ^ t.card ≤ U := by
  calc
    p ^ t.card = ∏ _q ∈ t, p := by rw [Finset.prod_const]
    _ ≤ ∏ q ∈ t, q := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hsmall
    _ ≤ v := Nat.le_of_dvd hv (prod_primeFactors_subset_dvd ht)
    _ ≤ U := hvU

/-- Uniform nine-tenths preservation at every scale at least 511. -/
theorem totientDensity_lcm_gt_nine_tenths_of_large_signature
    {u v s p : ℕ} {ps : List ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hs : 511 ≤ s) (hp : 2 * s + 3 ≤ p) (hvU : v ≤ 4 ^ s)
    (hcover : ∀ q, q.Prime → Odd q → q < p → q ∈ ps)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  have hsmall := missingPrime_ge_of_odd_signature_eq hu hvodd hcover hcode
  have hpow := primeFactors_subset_pow_card_le hv hvU Finset.sdiff_subset hsmall
  have hfac := thresholdFactor_pow_gt_nine_tenths_of_large_scale hs hp hpow
  have htail := totientDensity_lcm_ge_tailFactor hu hv (by omega) hsmall
    (show (v.primeFactors \ u.primeFactors).card ≤
      (v.primeFactors \ u.primeFactors).card from le_rfl)
  have hstrict := mul_lt_mul_of_pos_left hfac (totientDensity_pos hu)
  exact lt_of_lt_of_le (by simpa [mul_comm] using hstrict) htail

/-- The concrete `s`-coordinate version of the large-scale tail theorem. -/
theorem totientDensity_lcm_gt_nine_tenths_of_oddTailCoordinates
    {u v s : ℕ} (hu : 0 < u) (hv : 0 < v) (hvodd : Odd v)
    (hs : 511 ≤ s) (hvU : v ≤ 4 ^ s)
    (hcode : divisorSignatureCode (oddTailCoordinates s) u =
      divisorSignatureCode (oddTailCoordinates s) v) :
    (9 / 10 : ℚ) * totientDensity u < totientDensity (Nat.lcm u v) := by
  exact totientDensity_lcm_gt_nine_tenths_of_large_signature hu hv hvodd hs
    (le_refl (2 * s + 3)) hvU
    (fun _ hq hodd hqs => oddTailCoordinates_covers hq hodd hqs) hcode

end Erdos883Verified

#print axioms Erdos883Verified.ten_mul_lt_of_pow_le_four_pow
#print axioms Erdos883Verified.thresholdFactor_pow_ge_one_sub_ratio
#print axioms Erdos883Verified.thresholdFactor_pow_gt_nine_tenths
#print axioms Erdos883Verified.thresholdFactor_pow_gt_nine_tenths_of_large_scale

#print axioms Erdos883Verified.oddTailCoordinates_length
#print axioms Erdos883Verified.oddTailCoordinates_covers
#print axioms Erdos883Verified.missingPrime_ge_of_odd_signature_eq
#print axioms Erdos883Verified.primeFactors_subset_pow_card_le
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_large_signature
#print axioms Erdos883Verified.totientDensity_lcm_gt_nine_tenths_of_oddTailCoordinates
