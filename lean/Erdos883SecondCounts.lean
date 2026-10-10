import Erdos883NeighborDiscrepancy
import Erdos883SecondPrimeSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Independent candidate counting for the near-U construction. All counts are
actual finite prefix counts, and the imported first-question inclusion-exclusion
lemmas retain their original provenance. -/

namespace Erdos883Second.Near

open Erdos883Verified

theorem totientDensity_mul_ge {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    totientDensity u * totientDensity v ≤ totientDensity (u * v) := by
  have hh : ((Nat.totient u : ℚ) * Nat.totient v) ≤ Nat.totient (u * v) := by
    exact_mod_cast Nat.totient_super_multiplicative u v
  have hden : (0 : ℚ) < (u : ℚ) * v :=
    mul_pos (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hv)
  unfold totientDensity
  push_cast
  rw [div_mul_div_comm]
  exact div_le_div_of_nonneg_right hh hden.le

theorem totientDensity_mul_eq {u v : ℕ} (hc : Nat.Coprime u v) :
    totientDensity (u * v) = totientDensity u * totientDensity v := by
  simp only [totientDensity, Nat.totient_mul hc, Nat.cast_mul, div_mul_div_comm]

theorem totientDensity_two_mul {a : ℕ} (ha : Odd a) :
    totientDensity (2 * a) = totientDensity a / 2 := by
  rw [totientDensity_mul_eq ha.coprime_two_left]
  norm_num [totientDensity]
  ring

theorem discrepancy_le_two_pow (w : ℕ) :
    coprimeDiscrepancyError w ≤ 2 ^ w := by
  exact (Nat.sub_le _ _).trans
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le w 1))

/-- A coarse discrepancy with its error directly in prime-support form. -/
theorem coprimePrefixCount_ge_density_sub_two_pow (X q : ℕ) (hq : 0 < q) :
    (X : ℚ) * totientDensity q - (2 ^ q.primeFactors.card : ℕ) ≤
      (coprimePrefixCount X q : ℚ) := by
  have he : (coprimeDiscrepancyError q.primeFactors.card : ℚ) ≤
      (2 ^ q.primeFactors.card : ℕ) := by
    exact_mod_cast discrepancy_le_two_pow q.primeFactors.card
  exact (sub_le_sub_left he _).trans
    (coprimePrefixCount_ge_density_sub_error_of_pos X hq)

/-- Candidate left vertices are precisely three times the positive odd integers
up to `n/3` coprime to the apex. Coprimality with `2*a` enforces oddness. -/
def leftCandidates (n a : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (n / 3)).filter (fun w => Nat.Coprime w (2 * a))).image
    (fun w => 3 * w)

theorem leftCandidates_card (n a : ℕ) :
    (leftCandidates n a).card = coprimePrefixCount (n / 3) (2 * a) := by
  unfold leftCandidates coprimePrefixCount
  exact Finset.card_image_of_injective _ (by
    intro u v h; dsimp at h; omega)

theorem leftCandidates_mem {n a b : ℕ} (ha6 : Nat.Coprime a 6)
    (hb : b ∈ leftCandidates n a) :
    b ∈ Finset.Icc 1 n ∧ Odd b ∧ 3 ∣ b ∧ Nat.Coprime a b := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hwu, hwc⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw1, hwn⟩ := Finset.mem_Icc.mp hwu
  have hwodd : Odd w := Nat.coprime_two_right.mp
    (hwc.of_dvd_right (dvd_mul_right 2 a))
  have hwa : Nat.Coprime w a := hwc.of_dvd_right (dvd_mul_left a 2)
  have ha3 : Nat.Coprime a 3 := ha6.of_dvd_right (by decide)
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    (by decide : Odd 3).mul hwodd, dvd_mul_right 3 w,
    ha3.mul_right hwa.symm⟩

theorem two_mul_prime_support_card_le {a : ℕ} (ha : 0 < a) :
    (2 * a).primeFactors.card ≤ a.primeFactors.card + 1 := by
  rw [Nat.primeFactors_mul (by decide) ha.ne', Nat.prime_two.primeFactors,
    Finset.singleton_union]
  exact Finset.card_insert_le _ _

/-- Uniform lower bound for the left candidates with full rounding and error. -/
theorem leftCandidates_card_ge {n a : ℕ} (ha : 0 < a) (haodd : Odd a) :
    (n : ℚ) / 6 * totientDensity a -
      (2 * 2 ^ a.primeFactors.card : ℕ) - 1 ≤ (leftCandidates n a).card := by
  have hcount := coprimePrefixCount_ge_density_sub_two_pow
    (n / 3) (2 * a) (by omega)
  rw [totientDensity_two_mul haodd, ← leftCandidates_card] at hcount
  have heN : 2 ^ (2 * a).primeFactors.card ≤ 2 * 2 ^ a.primeFactors.card := by
    calc
      _ ≤ 2 ^ (a.primeFactors.card + 1) :=
        Nat.pow_le_pow_right (by decide) (two_mul_prime_support_card_le ha)
      _ = _ := by rw [pow_succ]; omega
  have he : ((2 ^ (2 * a).primeFactors.card : ℕ) : ℚ) ≤
      (2 * 2 ^ a.primeFactors.card : ℕ) := by exact_mod_cast heN
  have hn : (n : ℚ) / 3 - 1 ≤ ((n / 3 : ℕ) : ℚ) :=
    rat_div_sub_one_le_nat_div n 3 (by decide)
  have hm := mul_le_mul_of_nonneg_right hn
    (div_nonneg (totientDensity_nonneg a) (by norm_num : (0 : ℚ) ≤ 2))
  have hr := totientDensity_le_one a
  linarith

/-- Right candidates are the even integers up to `n` coprime to odd `q`. -/
def rightCandidates (n q : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (n / 2)).filter (fun w => Nat.Coprime w q)).image
    (fun w => 2 * w)

theorem rightCandidates_card (n q : ℕ) :
    (rightCandidates n q).card = coprimePrefixCount (n / 2) q := by
  unfold rightCandidates coprimePrefixCount
  exact Finset.card_image_of_injective _ (by
    intro u v h; dsimp at h; omega)

theorem rightCandidates_mem {n q c : ℕ} (hqodd : Odd q)
    (hc : c ∈ rightCandidates n q) :
    c ∈ Finset.Icc 1 n ∧ Even c ∧ Nat.Coprime c q := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hwu, hwc⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw1, hwn⟩ := Finset.mem_Icc.mp hwu
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    ⟨w, by omega⟩, (coprime_two_mul_iff_of_odd w hqodd).mpr hwc⟩

theorem rightCandidates_card_ge {n q : ℕ} (hq : 0 < q) :
    (n : ℚ) / 2 * totientDensity q -
      (2 ^ q.primeFactors.card : ℕ) - 1 ≤ (rightCandidates n q).card := by
  have hcount := coprimePrefixCount_ge_density_sub_two_pow (n / 2) q hq
  rw [← rightCandidates_card] at hcount
  have hn : (n : ℚ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℚ) :=
    rat_div_sub_one_le_nat_div n 2 (by decide)
  have hm := mul_le_mul_of_nonneg_right hn (totientDensity_nonneg q)
  have hr := totientDensity_le_one q
  linarith

#print axioms leftCandidates_card_ge
#print axioms rightCandidates_card_ge
#print axioms totientDensity_mul_ge

end Erdos883Second.Near
