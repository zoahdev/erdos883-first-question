import Erdos883SecondMoment
import Mathlib.Algebra.Order.Ring.Pow

namespace Erdos883Second.Near

set_option maxHeartbeats 2000000

open Erdos883Verified

def telescopeFactor (j : ℕ) : ℚ :=
  ((j + 2 : ℕ) : ℚ) ^ 2 / (((j + 2 : ℕ) : ℚ) ^ 2 - 1)

/-- An exact finite telescoping product. There is no infinite Euler product. -/
theorem telescopeFactor_prod (n : ℕ) :
    (∏ j ∈ Finset.range n, telescopeFactor j) =
      2 * ((n : ℚ) + 1) / ((n : ℚ) + 2) := by
  induction n with
  | zero => norm_num [telescopeFactor]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    dsimp [telescopeFactor]
    push_cast
    have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    have h2 : (n : ℚ) + 2 ≠ 0 := by positivity
    have h3 : (n : ℚ) + 3 ≠ 0 := by positivity
    have hs : ((n : ℚ) + 2) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring

theorem telescopeFactor_one_le (j : ℕ) : 1 ≤ telescopeFactor j := by
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  have hd : (0 : ℚ) < ((j + 2 : ℕ) : ℚ) ^ 2 - 1 := by
    push_cast
    nlinarith
  unfold telescopeFactor
  exact (le_div_iff₀ hd).mpr (by linarith)

theorem telescopeFactor_prod_le_two (n : ℕ) :
    (∏ j ∈ Finset.range n, telescopeFactor j) ≤ 2 := by
  rw [telescopeFactor_prod]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (n : ℚ) + 2)).mpr
  linarith

/-- A product over any bounded set of primes is bounded by the finite
telescoping product over all integers `2,...,n+1`. -/
theorem prime_telescope_prod_le_two (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hn : ∀ p ∈ P, p ≤ n) :
    (∏ p ∈ P, (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1)) ≤ 2 := by
  classical
  let S := P.image (fun p => p - 2)
  have hs : S ⊆ Finset.range n := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have hp2 := (hP p hp).two_le
    have hpn := hn p hp
    apply Finset.mem_range.mpr
    omega
  have hi : ∀ p ∈ P, ∀ q ∈ P, p - 2 = q - 2 → p = q := by
    intro p hp q hq he
    have hp2 := (hP p hp).two_le
    have hq2 := (hP q hq).two_le
    omega
  have he : (∏ j ∈ S, telescopeFactor j) =
      ∏ p ∈ P, (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) := by
    dsimp [S]
    rw [Finset.prod_image hi]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 := (hP p hp).two_le
    simp [telescopeFactor, Nat.sub_add_cancel hp2]
  rw [← he]
  calc
    _ ≤ ∏ j ∈ Finset.range n, telescopeFactor j := by
      apply Finset.prod_le_prod_of_subset_of_one_le hs
      · intro j hj; exact (telescopeFactor_one_le j).trans' (by norm_num)
      · intro j hj _; exact telescopeFactor_one_le j
    _ ≤ 2 := telescopeFactor_prod_le_two n

theorem moment_euler_factor_le_telescope {k p : ℕ} (hp : p.Prime) :
    1 + momentWeight k p / p ≤
      ((p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1)) ^ momentExponent k := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < p := by linarith
  have hp2 : (0 : ℚ) < (p : ℚ) ^ 2 := sq_pos_of_pos hp0
  have hd : (0 : ℚ) < (p : ℚ) ^ 2 - 1 := by nlinarith
  have hb := one_add_mul_sub_le_pow
    (show (-1 : ℚ) ≤ 1 + 1 / (p : ℚ) ^ 2 by
      have h := div_nonneg (by norm_num : (0 : ℚ) ≤ 1) hp2.le
      linarith)
    (momentExponent k)
  have hb' : 1 + (momentExponent k : ℚ) / (p : ℚ) ^ 2 ≤
      (1 + 1 / (p : ℚ) ^ 2) ^ momentExponent k := by
    simpa only [add_sub_cancel_left, mul_one_div] using hb
  have hkernel : 1 + 1 / (p : ℚ) ^ 2 ≤
      (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) := by
    have hfrac := one_div_le_one_div_of_le hd
      (show (p : ℚ) ^ 2 - 1 ≤ (p : ℚ) ^ 2 by linarith)
    have he : 1 + 1 / ((p : ℚ) ^ 2 - 1) =
        (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) := by
      field_simp
      ring
    linarith
  calc
    _ ≤ 1 + (momentExponent k : ℚ) / (p : ℚ) ^ 2 :=
      by simpa only [add_comm] using add_le_add_left (momentWeight_div_le (k := k) hp) 1
    _ ≤ _ := hb'
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hkernel _

/-- Explicit uniform finite Euler bound for every moment order. -/
theorem moment_euler_prod_le_constant (n k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hn : ∀ p ∈ P, p ≤ n) :
    (∏ p ∈ P, (1 + momentWeight k p / p)) ≤ momentConstant k := by
  have hprod : (∏ p ∈ P, (1 + momentWeight k p / p)) ≤
      ∏ p ∈ P, ((p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1)) ^ momentExponent k := by
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg (by norm_num)
        (div_nonneg (momentWeight_nonneg (hP p hp)) (Nat.cast_nonneg p))
    · intro p hp; exact moment_euler_factor_le_telescope (hP p hp)
  calc
    _ ≤ _ := hprod
    _ = (∏ p ∈ P, (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1)) ^ momentExponent k :=
      Finset.prod_pow _ _ _
    _ ≤ (2 : ℚ) ^ momentExponent k :=
      pow_le_pow_left₀ (Finset.prod_nonneg fun p hp => by
        have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p hp).two_le
        apply div_nonneg (sq_nonneg _)
        nlinarith) (prime_telescope_prod_le_two n P hP hn) _
    _ = _ := rfl

/-- All primes that can divide a positive integer in the prefix. -/
def prefixPrimeSupport (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter Nat.Prime

theorem prefixPrimeSupport_contains {n v : ℕ} (hv : v ∈ Finset.Icc 1 n) :
    v.primeFactors ⊆ prefixPrimeSupport n := by
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨hv1, hvn⟩ := Finset.mem_Icc.mp hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpprime.two_le, ?_⟩, hpprime⟩
  exact (Nat.le_of_dvd hv1 (Nat.dvd_of_mem_primeFactors hp)).trans hvn

/-- The desired unconditional, all-positive-prefix arbitrary-order moment. -/
theorem inverse_totient_moment_le (n k : ℕ) :
    (∑ v ∈ Finset.Icc 1 n, (totientDensity v)⁻¹ ^ k) ≤
      momentConstant k * n := by
  let P := prefixPrimeSupport n
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp; exact (Finset.mem_filter.mp hp).2
  have hn : ∀ p ∈ P, p ≤ n := by
    intro p hp; exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  calc
    _ ≤ (n : ℚ) * ∏ p ∈ P, (1 + momentWeight k p / p) :=
      inverse_totient_moment_le_euler n k P hP
        (fun v hv => prefixPrimeSupport_contains hv)
    _ ≤ (n : ℚ) * momentConstant k :=
      mul_le_mul_of_nonneg_left (moment_euler_prod_le_constant n k P hP hn)
        (Nat.cast_nonneg n)
    _ = _ := by ring

#print axioms inverse_totient_moment_le
#print axioms moment_euler_prod_le_constant

end Erdos883Second.Near
