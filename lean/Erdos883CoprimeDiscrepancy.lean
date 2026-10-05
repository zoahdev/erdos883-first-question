import Erdos883CoprimeCounts
import Erdos883TotientDensity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Cast.Order.Field

namespace Erdos883Verified

open scoped ArithmeticFunction.Moebius
open Finset

/-- The divisor sum of the Möbius function detects the integer one. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- Divisor inclusion-exclusion is the coprimality indicator. -/
theorem sum_moebius_common_divisors (w D : ℕ) (hD : D ≠ 0) :
    ∑ d ∈ D.divisors, (if d ∣ w then μ d else 0) =
      if Nat.Coprime w D then 1 else 0 := by
  have hg : (Nat.gcd w D) ≠ 0 := (Nat.gcd_pos_of_pos_right w (Nat.pos_of_ne_zero hD)).ne'
  have heq : D.divisors.filter (fun d => d ∣ w) = (Nat.gcd w D).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdD, _⟩, hdw⟩
      exact ⟨⟨hdw, hdD⟩, hg⟩
    · rintro ⟨⟨hdw, hdD⟩, _⟩
      exact ⟨⟨hdD, hD⟩, hdw⟩
  rw [← Finset.sum_filter, heq, sum_moebius_divisors]

/-- Exact Möbius floor formula for a positive-modulus prefix count. -/
theorem coprimePrefixCount_eq_moebius_sum (X D : ℕ) (hD : D ≠ 0) :
    (coprimePrefixCount X D : ℤ) =
      ∑ d ∈ D.divisors, μ d * (X / d : ℕ) := by
  calc
    (coprimePrefixCount X D : ℤ) =
        ∑ w ∈ Finset.Icc 1 X, (if Nat.Coprime w D then (1 : ℤ) else 0) := by
      simp [coprimePrefixCount]
    _ = ∑ w ∈ Finset.Icc 1 X, ∑ d ∈ D.divisors,
        (if d ∣ w then μ d else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (sum_moebius_common_divisors w D hD).symm
    _ = ∑ d ∈ D.divisors, ∑ w ∈ Finset.Icc 1 X,
        (if d ∣ w then μ d else 0) := Finset.sum_comm
    _ = ∑ d ∈ D.divisors, μ d * (X / d : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      have hcard : ((Finset.Icc 1 X).filter (fun w => d ∣ w)).card = X / d := by
        have heq : Finset.Icc 1 X = Finset.Ioc 0 X := by
          ext w
          simp only [Finset.mem_Icc, Finset.mem_Ioc]
          omega
        rw [heq, Nat.Ioc_filter_dvd_card_eq_div]
      simp [hcard, mul_comm]

/-- The density is the squarefree Möbius reciprocal divisor sum. -/
theorem totientDensity_eq_moebius_sum {D : ℕ} (hD : Squarefree D) :
    totientDensity D = ∑ d ∈ D.divisors, (μ d : ℚ) / (d : ℚ) := by
  let f : ArithmeticFunction ℚ := ⟨fun n => (n : ℚ)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro m n h
      simp [f, Nat.cast_mul, mul_comm]
  rw [totientDensity_eq_prod (Nat.pos_of_ne_zero hD.ne_zero)]
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hD
  simpa [f, div_eq_mul_inv] using h

/-- A squarefree integer has two choices for each prime divisor. -/
theorem card_divisors_squarefree {D : ℕ} (hD : Squarefree D) :
    D.divisors.card = 2 ^ D.primeFactors.card := by
  rw [Nat.card_divisors hD.ne_zero]
  calc
    ∏ p ∈ D.primeFactors, (D.factorization p + 1) =
        ∏ p ∈ D.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hD
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ D.primeFactors.card := by simp

/-- On squarefree divisors the Möbius function has one of the two signs. -/
theorem moebius_divisor_eq_one_or_neg_one {D d : ℕ} (hD : Squarefree D)
    (hd : d ∈ D.divisors) : μ d = 1 ∨ μ d = -1 := by
  apply ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
  exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
    (hD.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))

/-- Half the divisors of a nontrivial squarefree integer have positive Möbius sign. -/
theorem positive_moebius_divisors_card {D : ℕ} (hD : Squarefree D) (hD1 : 1 < D) :
    (D.divisors.filter (fun d => μ d = 1)).card = 2 ^ (D.primeFactors.card - 1) := by
  have hsum : (∑ d ∈ D.divisors, μ d) = 0 := by
    rw [sum_moebius_divisors, if_neg (by omega)]
  have hc : (D.divisors.card : ℤ) =
      2 * ((D.divisors.filter (fun d => μ d = 1)).card : ℤ) := by
    calc
      (D.divisors.card : ℤ) = ∑ d ∈ D.divisors, (μ d + 1) := by
        rw [Finset.sum_add_distrib, hsum]
        simp
      _ = ∑ d ∈ D.divisors, (if μ d = 1 then (2 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rcases moebius_divisor_eq_one_or_neg_one hD hd with h | h
        · simp [h]
        · simp [h]
      _ = 2 * ((D.divisors.filter (fun d => μ d = 1)).card : ℤ) := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
  have hc' : D.divisors.card =
      2 * (D.divisors.filter (fun d => μ d = 1)).card := by exact_mod_cast hc
  rw [card_divisors_squarefree hD] at hc'
  have hw : 0 < D.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hD1)
  have hpow : 2 ^ D.primeFactors.card = 2 * 2 ^ (D.primeFactors.card - 1) := by
    conv_lhs => rw [show D.primeFactors.card = (D.primeFactors.card - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  rw [hpow] at hc'
  omega

/-- Removing the exact divisor-one term saves one in the one-sided error. -/
theorem nontrivial_positive_moebius_divisors_card {D : ℕ}
    (hD : Squarefree D) (hD1 : 1 < D) :
    ((D.divisors.filter (fun d => μ d = 1)).erase 1).card =
      2 ^ (D.primeFactors.card - 1) - 1 := by
  rw [Finset.card_erase_of_mem, positive_moebius_divisors_card hD hD1]
  simp [hD.ne_zero]

/-- The exact floor formula after casting into the rationals. -/
theorem coprimePrefixCount_eq_moebius_sum_rat (X D : ℕ) (hD : D ≠ 0) :
    (coprimePrefixCount X D : ℚ) =
      ∑ d ∈ D.divisors, (μ d : ℚ) * ((X / d : ℕ) : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (coprimePrefixCount_eq_moebius_sum X D hD)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h

/-- A rational quotient exceeds its natural floor by less than one. -/
theorem rat_div_sub_one_le_nat_div (X d : ℕ) (hd : 0 < d) :
    (X : ℚ) / (d : ℚ) - 1 ≤ ((X / d : ℕ) : ℚ) := by
  have hn : X < (X / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (X / d))
  have hq : (X : ℚ) < (((X / d : ℕ) : ℚ) + 1) * (d : ℚ) := by
    exact_mod_cast hn
  have hr : (X : ℚ) / (d : ℚ) < ((X / d : ℕ) : ℚ) + 1 :=
    (div_lt_iff₀ (Nat.cast_pos.mpr hd)).mpr hq
  linarith

/-- The sharp uniform one-sided inclusion-exclusion error for squarefree moduli. -/
theorem coprimePrefixCount_ge_density_sub_error (X : ℕ) {D : ℕ}
    (hD : Squarefree D) (hD1 : 1 < D) :
    (X : ℚ) * totientDensity D -
      ((2 ^ (D.primeFactors.card - 1) - 1 : ℕ) : ℚ) ≤ coprimePrefixCount X D := by
  let bad := (D.divisors.filter (fun d => μ d = 1)).erase 1
  have hbadcard : bad.card = 2 ^ (D.primeFactors.card - 1) - 1 :=
    nontrivial_positive_moebius_divisors_card hD hD1
  have hpoint (d : ℕ) (hd : d ∈ D.divisors) :
      (μ d : ℚ) * ((X : ℚ) / (d : ℚ) - ((X / d : ℕ) : ℚ)) ≤
        if d ∈ bad then (1 : ℚ) else 0 := by
    by_cases hd1 : d = 1
    · subst d
      simp [bad]
    · rcases moebius_divisor_eq_one_or_neg_one hD hd with h | h
      · simp only [h, Int.cast_one, one_mul]
        have hb : d ∈ bad := by simp [bad, hd, hd1, h]
        rw [if_pos hb]
        have := rat_div_sub_one_le_nat_div X d (Nat.pos_of_mem_divisors hd)
        linarith
      · simp only [h, Int.cast_neg, Int.cast_one, neg_one_mul]
        have hb : d ∉ bad := by simp [bad, h]
        rw [if_neg hb]
        have hu : ((X / d : ℕ) : ℚ) ≤ (X : ℚ) / (d : ℚ) := Nat.cast_div_le
        linarith
  have hsum : (X : ℚ) * totientDensity D - coprimePrefixCount X D ≤ (bad.card : ℚ) := by
    calc
      (X : ℚ) * totientDensity D - coprimePrefixCount X D =
          ∑ d ∈ D.divisors,
            (μ d : ℚ) * ((X : ℚ) / (d : ℚ) - ((X / d : ℕ) : ℚ)) := by
        rw [totientDensity_eq_moebius_sum hD,
          coprimePrefixCount_eq_moebius_sum_rat X D hD.ne_zero,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ ≤ ∑ d ∈ D.divisors, (if d ∈ bad then (1 : ℚ) else 0) :=
        Finset.sum_le_sum hpoint
      _ = (bad.card : ℚ) := by
        rw [← Finset.sum_filter]
        have heq : D.divisors.filter (fun d => d ∈ bad) = bad := by
          ext d
          simp [bad, and_assoc, and_left_comm]
        rw [heq]
        simp
  rw [hbadcard] at hsum
  linarith

/-- Modulus one is exact and requires no discrepancy allowance. -/
theorem coprimePrefixCount_one (X : ℕ) : coprimePrefixCount X 1 = X := by
  simp [coprimePrefixCount]

/-- The rational density formula is exact at modulus one. -/
theorem coprimePrefixCount_one_eq_density (X : ℕ) :
    (coprimePrefixCount X 1 : ℚ) = (X : ℚ) * totientDensity 1 := by
  simp [coprimePrefixCount_one, totientDensity]

#print axioms sum_moebius_divisors
#print axioms sum_moebius_common_divisors
#print axioms coprimePrefixCount_eq_moebius_sum
#print axioms totientDensity_eq_moebius_sum
#print axioms card_divisors_squarefree
#print axioms moebius_divisor_eq_one_or_neg_one
#print axioms positive_moebius_divisors_card
#print axioms nontrivial_positive_moebius_divisors_card
#print axioms coprimePrefixCount_eq_moebius_sum_rat
#print axioms rat_div_sub_one_le_nat_div
#print axioms coprimePrefixCount_ge_density_sub_error
#print axioms coprimePrefixCount_one
#print axioms coprimePrefixCount_one_eq_density

end Erdos883Verified
