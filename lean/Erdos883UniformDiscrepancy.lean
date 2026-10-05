import Erdos883CoprimeDiscrepancy
import Mathlib.Analysis.Real.Sqrt

namespace Erdos883Verified

open Finset

/-- Only five odd primes are smaller than seventeen. -/
theorem odd_prime_lt_seventeen {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hlt : p < 17) : p ∈ ({3, 5, 7, 11, 13} : Finset ℕ) := by
  have hp2 := hp.two_le
  have hoddmod : p % 2 = 1 := Nat.odd_iff.mp hodd
  have h : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 9 ∨ p = 11 ∨ p = 13 ∨ p = 15 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *
  all_goals exact absurd hp (by decide)

/-- The product of `16/p` over arbitrary distinct odd primes is less than 81. -/
theorem odd_prime_finset_ratio_lt (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    (∏ p ∈ s, (16 : ℚ) / p) < 81 := by
  let t : Finset ℕ := {3, 5, 7, 11, 13}
  have hnonneg (p : ℕ) : 0 ≤ (16 : ℚ) / p := by positivity
  have hlarge (p : ℕ) (hp : p ∈ s) (hnt : p ∉ t) : (16 : ℚ) / p ≤ 1 := by
    have h17 : 17 ≤ p := by
      by_contra h
      exact hnt (odd_prime_lt_seventeen (hs p hp).1 (hs p hp).2 (by omega))
    apply (div_le_one₀ (by exact_mod_cast (hs p hp).1.pos)).2
    exact_mod_cast (show 16 ≤ p by omega)
  have hsmall : (∏ p ∈ s ∩ t, (16 : ℚ) / p) ≤ ∏ p ∈ t, (16 : ℚ) / p := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.inter_subset_right)
    · exact fun p _ => hnonneg p
    · intro p hp _
      simp only [t, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  calc
    (∏ p ∈ s, (16 : ℚ) / p) ≤ ∏ p ∈ s ∩ t, (16 : ℚ) / p := by
      apply Finset.prod_le_prod_of_subset_of_le_one (Finset.inter_subset_left)
      · exact fun p _ => hnonneg p
      · intro p hp hnot
        exact hlarge p hp (fun ht => hnot (Finset.mem_inter.mpr ⟨hp, ht⟩))
    _ ≤ ∏ p ∈ t, (16 : ℚ) / p := hsmall
    _ < 81 := by norm_num [t]

/-- A useful integral form of the five-small-prime product bound. -/
theorem odd_prime_finset_pow_four_lt (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    (2 ^ s.card) ^ 4 < 81 * ∏ p ∈ s, p := by
  have hr := odd_prime_finset_ratio_lt s hs
  have hp : 0 < (∏ p ∈ s, p : ℕ) :=
    Finset.prod_pos (fun p hp => (hs p hp).1.pos)
  have heq : (∏ p ∈ s, (16 : ℚ) / p) =
      (16 : ℚ) ^ s.card / (∏ p ∈ s, p : ℕ) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [heq] at hr
  have hq := (div_lt_iff₀ (show (0 : ℚ) < (∏ p ∈ s, p : ℕ) by exact_mod_cast hp)).mp hr
  have hn : 16 ^ s.card < 81 * ∏ p ∈ s, p := by exact_mod_cast hq
  have he : (2 ^ s.card) ^ 4 = 16 ^ s.card := by
    rw [← pow_mul, Nat.mul_comm s.card 4, pow_mul]
    norm_num
  rwa [he]

/-- The fourth power of the divisor-support factor is bounded for every positive odd modulus. -/
theorem odd_primeFactors_pow_four_lt {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    (2 ^ n.primeFactors.card) ^ 4 < 81 * n := by
  have hprod := odd_prime_finset_pow_four_lt n.primeFactors (by
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp,
      hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩)
  exact hprod.trans_le (Nat.mul_le_mul_left 81
    (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))

/-- Endpoints bounded by `U` give the squared-scale fourth-power bound. -/
theorem odd_lcm_primeFactors_pow_four_lt {u v U : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U) :
    (2 ^ (Nat.lcm u v).primeFactors.card) ^ 4 < 81 * U ^ 2 := by
  have hlcm : Odd (Nat.lcm u v) :=
    (huodd.mul hvodd).of_dvd_nat (Nat.lcm_dvd_mul u v)
  have hbound : Nat.lcm u v ≤ U ^ 2 := by
    calc
      Nat.lcm u v ≤ u * v := Nat.lcm_le_mul hu hv
      _ ≤ U * U := Nat.mul_le_mul huU hvU
      _ = U ^ 2 := by ring
  exact (odd_primeFactors_pow_four_lt (Nat.lcm_pos hu hv) hlcm).trans_le
    (Nat.mul_le_mul_left 81 hbound)

/-- Even at zero prime support, twice the sharp error is smaller than `2^w`. -/
theorem twice_sharp_error_lt_two_pow (w : ℕ) :
    2 * (2 ^ (w - 1) - 1) < 2 ^ w := by
  cases w with
  | zero => norm_num
  | succ w =>
    simp only [Nat.add_one_sub_one, pow_succ]
    have hw : 0 < (2 : ℕ) ^ w := pow_pos (by norm_num) _
    omega

/-- An entirely integral version of the uniform square-root discrepancy estimate. -/
theorem odd_lcm_sharp_error_sq_lt {u v U : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U) :
    4 * (2 ^ ((Nat.lcm u v).primeFactors.card - 1) - 1) ^ 2 < 9 * U := by
  let w := (Nat.lcm u v).primeFactors.card
  have hfour : ((2 : ℕ) ^ w) ^ 4 < 81 * U ^ 2 :=
    odd_lcm_primeFactors_pow_four_lt hu hv huodd hvodd huU hvU
  have hsq : ((2 : ℕ) ^ w) ^ 2 < 9 * U := by
    apply lt_of_pow_lt_pow_left' 2
    nlinarith only [hfour]
  have herr := twice_sharp_error_lt_two_pow w
  have herrsq : (2 * (2 ^ (w - 1) - 1)) ^ 2 < ((2 : ℕ) ^ w) ^ 2 :=
    Nat.pow_lt_pow_left herr (by decide)
  dsimp [w] at *
  nlinarith only [herrsq, hsq]

/-- The squared error estimate, directly usable with rational density bounds. -/
theorem odd_lcm_sharp_error_sq_lt_rat {u v U : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U) :
    (((2 ^ ((Nat.lcm u v).primeFactors.card - 1) - 1 : ℕ) : ℚ)) ^ 2 <
      (9 / 4 : ℚ) * U := by
  have hn := odd_lcm_sharp_error_sq_lt hu hv huodd hvodd huU hvU
  have hq : (4 : ℚ) * (((2 ^ ((Nat.lcm u v).primeFactors.card - 1) - 1 : ℕ) : ℚ)) ^ 2 <
      9 * U := by exact_mod_cast hn
  linarith

/-- The uniform discrepancy is strictly smaller than three halves of `√U`. -/
theorem odd_lcm_sharp_error_lt_three_halves_sqrt {u v U : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huodd : Odd u) (hvodd : Odd v)
    (huU : u ≤ U) (hvU : v ≤ U) :
    ((2 ^ ((Nat.lcm u v).primeFactors.card - 1) - 1 : ℕ) : ℝ) <
      (3 / 2 : ℝ) * Real.sqrt U := by
  have hn := odd_lcm_sharp_error_sq_lt hu hv huodd hvodd huU hvU
  have hr : (4 : ℝ) * (((2 ^ ((Nat.lcm u v).primeFactors.card - 1) - 1 : ℕ) : ℝ)) ^ 2 <
      9 * U := by exact_mod_cast hn
  have hs : (Real.sqrt (U : ℝ)) ^ 2 = U := Real.sq_sqrt (Nat.cast_nonneg U)
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  nlinarith only [hr, hs]

#print axioms odd_prime_lt_seventeen
#print axioms odd_prime_finset_ratio_lt
#print axioms odd_prime_finset_pow_four_lt
#print axioms odd_primeFactors_pow_four_lt
#print axioms odd_lcm_primeFactors_pow_four_lt
#print axioms twice_sharp_error_lt_two_pow
#print axioms odd_lcm_sharp_error_sq_lt
#print axioms odd_lcm_sharp_error_sq_lt_rat
#print axioms odd_lcm_sharp_error_lt_three_halves_sqrt

end Erdos883Verified
