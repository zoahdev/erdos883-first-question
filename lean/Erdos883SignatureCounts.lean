import Erdos883CoprimeDiscrepancy
import Erdos883ParityCounts
import Erdos883PrimeSignatures
import Erdos883TotientMoment
import CdfDefinitions
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FinCases

namespace Erdos883Verified
open scoped ArithmeticFunction.Moebius
open Finset

/-- Odd multiples of a fixed positive odd factor are a scaling image. -/
theorem oddUniverse_multiples_eq_image (n : ℕ) {D : ℕ}
    (hD : 0 < D) (hodd : Odd D) :
    (oddUniverse n).filter (fun v => D ∣ v) =
      (oddUniverse (n / D)).image (fun k => D * k) := by
  ext v
  simp only [oddUniverse, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨hvpos, hvn⟩, hvodd⟩, ⟨k, rfl⟩⟩
    refine ⟨k, ⟨⟨?_, ?_⟩, Nat.Odd.of_mul_right hvodd⟩, rfl⟩
    · by_contra h
      have hk : k = 0 := by omega
      simp [hk] at hvpos
    · exact (Nat.le_div_iff_mul_le hD).mpr (by simpa [Nat.mul_comm] using hvn)
  · rintro ⟨k, ⟨⟨hkpos, hkn⟩, hkodd⟩, rfl⟩
    refine ⟨⟨⟨Nat.mul_pos hD hkpos, ?_⟩, hodd.mul hkodd⟩, dvd_mul_right D k⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hD).mp hkn

/-- Exact odd-multiple count in a finite prefix. -/
theorem oddUniverse_multiples_card (n : ℕ) {D : ℕ}
    (hD : 0 < D) (hodd : Odd D) :
    ((oddUniverse n).filter (fun v => D ∣ v)).card = ((n / D) + 1) / 2 := by
  rw [oddUniverse_multiples_eq_image n hD hodd,
    Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hD h),
    oddUniverse_card]
  rfl

/-- Rounding an odd multiple loses at most one half, uniformly in the modulus. -/
theorem oddMultiple_rounding_error (n D : ℕ) (hD : 0 < D) :
    |((((n / D) + 1) / 2 : ℕ) : ℚ) - (n : ℚ) / (2 * D)| ≤ 1 / 2 := by
  let q := n / D
  let k := (q + 1) / 2
  have hqlo : q * D ≤ n := Nat.div_mul_le_self n D
  have hqhi : n < (q + 1) * D :=
    (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self q)
  have hklo : 2 * k ≤ q + 1 := by dsimp [k]; omega
  have hkhi : q < 2 * k + 1 := by dsimp [k]; omega
  have hl : n < (2 * k + 1) * D := by nlinarith
  have hu : 2 * k * D ≤ n + D := by nlinarith
  have hlq : (n : ℚ) < (2 * (k : ℚ) + 1) * D := by exact_mod_cast hl
  have huq : 2 * (k : ℚ) * D ≤ (n : ℚ) + D := by exact_mod_cast hu
  have hDq : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  change |(k : ℚ) - (n : ℚ) / (2 * D)| ≤ 1 / 2
  apply abs_le.mpr
  constructor
  · have h' : (n : ℚ) / (2 * D) < k + 1 / 2 := by
      apply (div_lt_iff₀ (show (0 : ℚ) < 2 * D by positivity)).mpr
      nlinarith
    linarith
  · have h' : (k : ℚ) - 1 / 2 ≤ (n : ℚ) / (2 * D) := by
      apply (le_div_iff₀ (show (0 : ℚ) < 2 * D by positivity)).mpr
      nlinarith
    linarith

/-- Every odd arithmetic progression through zero has discrepancy at most one half. -/
theorem oddUniverse_multiples_error (n : ℕ) {D : ℕ}
    (hD : 0 < D) (hodd : Odd D) :
    |(((oddUniverse n).filter (fun v => D ∣ v)).card : ℚ) -
      (n : ℚ) / (2 * D)| ≤ 1 / 2 := by
  rw [oddUniverse_multiples_card n hD hodd]
  exact oddMultiple_rounding_error n D hD

/-- Odd vertices divisible by `A` and avoiding every prime factor of `B`. -/
def oddCoprimeMultiplesCount (n A B : ℕ) : ℕ :=
  ((oddUniverse n).filter (fun v => A ∣ v ∧ Nat.Coprime v B)).card

/-- Exact inclusion-exclusion for odd vertices with a prescribed divisible part. -/
theorem oddCoprimeMultiplesCount_eq_moebius_sum
    (n A B : ℕ) (hB : B ≠ 0) (hAB : Nat.Coprime A B) :
    (oddCoprimeMultiplesCount n A B : ℤ) =
      ∑ d ∈ B.divisors, μ d *
        (((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℤ) := by
  calc
    (oddCoprimeMultiplesCount n A B : ℤ) =
        ∑ v ∈ (oddUniverse n).filter (fun v => A ∣ v),
          (if Nat.Coprime v B then (1 : ℤ) else 0) := by
      simp [oddCoprimeMultiplesCount, Finset.filter_filter]
    _ = ∑ v ∈ (oddUniverse n).filter (fun v => A ∣ v),
        ∑ d ∈ B.divisors, (if d ∣ v then μ d else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (sum_moebius_common_divisors v B hB).symm
    _ = ∑ d ∈ B.divisors,
        ∑ v ∈ (oddUniverse n).filter (fun v => A ∣ v),
          (if d ∣ v then μ d else 0) := Finset.sum_comm
    _ = ∑ d ∈ B.divisors, μ d *
        (((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      have hAd : Nat.Coprime A d := hAB.of_dvd_right (Nat.dvd_of_mem_divisors hd)
      have heq : ((oddUniverse n).filter (fun v => A ∣ v)).filter
          (fun v => d ∣ v) = (oddUniverse n).filter (fun v => A * d ∣ v) := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hv, hAv⟩, hdv⟩
          exact ⟨hv, hAd.mul_dvd_of_dvd_of_dvd hAv hdv⟩
        · rintro ⟨hv, hmul⟩
          exact ⟨⟨hv, (dvd_mul_right A d).trans hmul⟩,
            (dvd_mul_left d A).trans hmul⟩
      rw [heq]
      simp [mul_comm]

/-- Rational form of exact odd-vertex inclusion-exclusion. -/
theorem oddCoprimeMultiplesCount_eq_moebius_sum_rat
    (n A B : ℕ) (hB : B ≠ 0) (hAB : Nat.Coprime A B) :
    (oddCoprimeMultiplesCount n A B : ℚ) =
      ∑ d ∈ B.divisors, (μ d : ℚ) *
        (((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (oddCoprimeMultiplesCount_eq_moebius_sum n A B hB hAB)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h

/-- Uniform signature discrepancy: one half for each excluded-divisor term. -/
theorem oddCoprimeMultiplesCount_error
    (n : ℕ) {A B : ℕ} (hA : 0 < A) (hAo : Odd A)
    (hB : Squarefree B) (hBo : Odd B) (hAB : Nat.Coprime A B) :
    |(oddCoprimeMultiplesCount n A B : ℚ) -
      (n : ℚ) / (2 * A) * totientDensity B| ≤
      (2 : ℚ) ^ B.primeFactors.card / 2 := by
  have heq : (oddCoprimeMultiplesCount n A B : ℚ) -
      (n : ℚ) / (2 * A) * totientDensity B =
      ∑ d ∈ B.divisors, (μ d : ℚ) *
        ((((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℚ) -
          (n : ℚ) / (2 * (A * d))) := by
    rw [oddCoprimeMultiplesCount_eq_moebius_sum_rat n A B hB.ne_zero hAB,
      totientDensity_eq_moebius_sum hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq]
  calc
    |∑ d ∈ B.divisors, (μ d : ℚ) *
        ((((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℚ) -
          (n : ℚ) / (2 * (A * d)))| ≤
        ∑ d ∈ B.divisors, |(μ d : ℚ) *
          ((((oddUniverse n).filter (fun v => A * d ∣ v)).card : ℚ) -
            (n : ℚ) / (2 * (A * d)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ B.divisors, (1 / 2 : ℚ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdo : Odd d := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors hd
        rw [hk] at hBo
        exact Nat.Odd.of_mul_left hBo
      have herr := oddUniverse_multiples_error n
        (Nat.mul_pos hA (Nat.pos_of_mem_divisors hd)) (hAo.mul hdo)
      rcases moebius_divisor_eq_one_or_neg_one hB hd with h | h
      · simpa only [h, Int.cast_one, one_mul, Nat.cast_mul] using herr
      · simpa only [h, Int.cast_neg, Int.cast_one, neg_one_mul, abs_neg, Nat.cast_mul] using herr
    _ = (2 : ℚ) ^ B.primeFactors.card / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, card_divisors_squarefree hB,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

#print axioms oddUniverse_multiples_eq_image
#print axioms oddUniverse_multiples_card
#print axioms oddMultiple_rounding_error
#print axioms oddUniverse_multiples_error
#print axioms oddCoprimeMultiplesCount_eq_moebius_sum
#print axioms oddCoprimeMultiplesCount_eq_moebius_sum_rat
#print axioms oddCoprimeMultiplesCount_error

/-- The four small odd primes, with bit 3 corresponding to the prime 3. -/
def fourPrimeSet : Finset ℕ := {3, 5, 7, 11}

/-- Selected prime supports in big-endian divisibility-code order. -/
def fourPrimeSelected (c : Fin 16) : Finset ℕ :=
  ([∅, {11}, {7}, {7, 11}, {5}, {5, 11}, {5, 7}, {5, 7, 11},
    {3}, {3, 11}, {3, 7}, {3, 7, 11}, {3, 5}, {3, 5, 11},
    {3, 5, 7}, {3, 5, 7, 11}] : List (Finset ℕ)).get c

def fourPrimeA (c : Fin 16) : ℕ := ∏ p ∈ fourPrimeSelected c, p
def fourPrimeB (c : Fin 16) : ℕ := ∏ p ∈ fourPrimeSet \ fourPrimeSelected c, p
def fourPrimeQ (c : Fin 16) : ℚ := totientDensity (fourPrimeB c) / fourPrimeA c
def fourPrimeSmallDensity (c : Fin 16) : ℚ := totientDensity (fourPrimeA c)
def fourPrimeError (c : Fin 16) : ℚ := (2 : ℚ) ^ (4 - (fourPrimeSelected c).card) / 2

def fourPrimeState (c : Fin 16) : Rat × Rat :=
  states.get ⟨c.val, by rw [states_count]; exact c.isLt⟩

theorem fourPrimeSet_prime : ∀ p ∈ fourPrimeSet, Nat.Prime p := by
  intro p hp
  simp only [fourPrimeSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem fourPrimeSelected_subset (c : Fin 16) : fourPrimeSelected c ⊆ fourPrimeSet := by
  revert c
  decide +kernel

theorem fourPrimeSelected_injective : Function.Injective fourPrimeSelected := by
  decide +kernel

theorem fourPrimeA_pos (c : Fin 16) : 0 < fourPrimeA c := by
  revert c
  decide +kernel

theorem fourPrimeA_odd (c : Fin 16) : Odd (fourPrimeA c) := by
  revert c
  decide +kernel

theorem fourPrimeB_odd (c : Fin 16) : Odd (fourPrimeB c) := by
  revert c
  decide +kernel

theorem fourPrimeB_squarefree (c : Fin 16) : Squarefree (fourPrimeB c) := by
  revert c
  decide +kernel

theorem fourPrimeAB_coprime (c : Fin 16) : Nat.Coprime (fourPrimeA c) (fourPrimeB c) := by
  revert c
  decide +kernel

theorem fourPrimeError_eq (c : Fin 16) :
    fourPrimeError c = (2 : ℚ) ^ (fourPrimeB c).primeFactors.card / 2 := by
  revert c
  decide +kernel

theorem fourPrimeQ_eq_state (c : Fin 16) : fourPrimeQ c = (fourPrimeState c).2 := by
  revert c
  decide +kernel

theorem fourPrimeSmallDensity_eq_state (c : Fin 16) :
    fourPrimeSmallDensity c = (fourPrimeState c).1 := by
  revert c
  decide +kernel

theorem fourPrimeError_sum : (∑ c : Fin 16, fourPrimeError c) = 81 / 2 := by
  decide +kernel

/-- Every odd vertex belongs to precisely the code prescribed by its four small primes. -/
def fourPrimeCode (v : ℕ) : Fin 16 :=
  ⟨divisorSignatureCode [3, 5, 7, 11] v,
    by simpa using divisorSignatureCode_lt [3, 5, 7, 11] v⟩

theorem fourPrimeSelected_code (v : ℕ) :
    fourPrimeSelected (fourPrimeCode v) = fourPrimeSet.filter (fun p => p ∣ v) := by
  by_cases h3 : 3 ∣ v <;> by_cases h5 : 5 ∣ v <;>
    by_cases h7 : 7 ∣ v <;> by_cases h11 : 11 ∣ v <;>
    simp [fourPrimeCode, divisorSignatureCode, divisorSignatureBits, binarySignatureCode,
      fourPrimeSelected, fourPrimeSet, h3, h5, h7, h11, Finset.filter_insert,
      Finset.filter_singleton]

/-- The code is exactly the selected-divisor/unselected-coprimality condition. -/
theorem fourPrimeCode_eq_iff (v : ℕ) (c : Fin 16) :
    fourPrimeCode v = c ↔
      fourPrimeA c ∣ v ∧ Nat.Coprime v (fourPrimeB c) := by
  rw [← fourPrimeSelected_injective.eq_iff, fourPrimeSelected_code]
  constructor
  · intro h
    constructor
    · apply (prime_finset_prod_dvd_iff _
        (fun p hp => fourPrimeSet_prime p (fourPrimeSelected_subset c hp)) v).mpr
      intro p hp
      have hm : p ∈ fourPrimeSet.filter (fun q => q ∣ v) := h.symm ▸ hp
      exact (Finset.mem_filter.mp hm).2
    · apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      obtain ⟨hpP, hpS⟩ := Finset.mem_sdiff.mp hp
      apply Nat.Coprime.symm
      apply (fourPrimeSet_prime p hpP).coprime_iff_not_dvd.mpr
      intro hd
      exact hpS (h ▸ Finset.mem_filter.mpr ⟨hpP, hd⟩)
  · rintro ⟨hA, hB⟩
    ext p
    constructor
    · intro hp
      obtain ⟨hpP, hd⟩ := Finset.mem_filter.mp hp
      by_contra hpS
      have hc := Nat.coprime_prod_right_iff.mp hB p (Finset.mem_sdiff.mpr ⟨hpP, hpS⟩)
      exact (fourPrimeSet_prime p hpP).coprime_iff_not_dvd.mp hc.symm hd
    · intro hp
      exact Finset.mem_filter.mpr ⟨fourPrimeSelected_subset c hp,
        (prime_finset_prod_dvd_iff _
          (fun p hp => fourPrimeSet_prime p (fourPrimeSelected_subset c hp)) v).mp hA p hp⟩

/-- The small-prime density represented by the first state coordinate. -/
theorem fourPrimeSmallDensity_eq_prod (c : Fin 16) :
    fourPrimeSmallDensity c = ∏ p ∈ fourPrimeSelected c, (1 - (p : ℚ)⁻¹) := by
  rw [fourPrimeSmallDensity, totientDensity_eq_prod (fourPrimeA_pos c)]
  congr 1
  exact Nat.primeFactors_prod (fun p hp => fourPrimeSet_prime p (fourPrimeSelected_subset c hp))

/-- The exact number of odd vertices having a given four-prime signature. -/
def fourPrimeCount (n : ℕ) (c : Fin 16) : ℕ :=
  ((oddUniverse n).filter (fun v => fourPrimeCode v = c)).card

theorem fourPrimeCount_eq (n : ℕ) (c : Fin 16) :
    fourPrimeCount n c = oddCoprimeMultiplesCount n (fourPrimeA c) (fourPrimeB c) := by
  simp only [fourPrimeCount, oddCoprimeMultiplesCount, fourPrimeCode_eq_iff]

/-- The finite-state discrepancy in precisely the mass used by `states`. -/
theorem fourPrimeCount_error (n : ℕ) (c : Fin 16) :
    |(fourPrimeCount n c : ℚ) - fourPrimeQ c * n / 2| ≤ fourPrimeError c := by
  rw [fourPrimeCount_eq, fourPrimeError_eq]
  have h := oddCoprimeMultiplesCount_error n (fourPrimeA_pos c) (fourPrimeA_odd c)
    (fourPrimeB_squarefree c) (fourPrimeB_odd c) (fourPrimeAB_coprime c)
  convert h using 2 <;> unfold fourPrimeQ <;> ring

/-- Direct state-list form of the odd-vertex discrepancy. -/
theorem fourPrimeCount_state_error (n : ℕ) (c : Fin 16) :
    |(fourPrimeCount n c : ℚ) - (fourPrimeState c).2 * n / 2| ≤ fourPrimeError c := by
  rw [← fourPrimeQ_eq_state]
  exact fourPrimeCount_error n c

/-- A large prime is coprime to both pieces of every small-prime signature. -/
theorem fourPrime_coprime_largePrime {p : ℕ} (hp : p.Prime) (hlarge : 11 < p)
    (c : Fin 16) : Nat.Coprime p (fourPrimeA c) ∧ Nat.Coprime p (fourPrimeB c) := by
  have hcop (q : ℕ) (hq : q ∈ fourPrimeSet) : Nat.Coprime p q := by
    apply (Nat.coprime_primes hp (fourPrimeSet_prime q hq)).mpr
    simp only [fourPrimeSet, Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  constructor
  · exact Nat.coprime_prod_right_iff.mpr fun q hq => hcop q (fourPrimeSelected_subset c hq)
  · exact Nat.coprime_prod_right_iff.mpr fun q hq => hcop q (Finset.mem_sdiff.mp hq).1

/-- The signature fiber additionally restricted to multiples of a tail prime. -/
def fourPrimeMultipleCount (n p : ℕ) (c : Fin 16) : ℕ :=
  ((oddUniverse n).filter (fun v => fourPrimeCode v = c ∧ p ∣ v)).card

theorem fourPrimeMultipleCount_eq (n : ℕ) {p : ℕ} (hp : p.Prime) (hlarge : 11 < p)
    (c : Fin 16) :
    fourPrimeMultipleCount n p c =
      oddCoprimeMultiplesCount n (fourPrimeA c * p) (fourPrimeB c) := by
  unfold fourPrimeMultipleCount oddCoprimeMultiplesCount
  congr 1
  apply Finset.filter_congr
  intro v hv
  rw [fourPrimeCode_eq_iff]
  have hAp := (fourPrime_coprime_largePrime hp hlarge c).1.symm
  constructor
  · rintro ⟨⟨hA, hB⟩, hpv⟩
    exact ⟨hAp.mul_dvd_of_dvd_of_dvd hA hpv, hB⟩
  · rintro ⟨hmul, hB⟩
    exact ⟨⟨(dvd_mul_right (fourPrimeA c) p).trans hmul, hB⟩,
      (dvd_mul_left p (fourPrimeA c)).trans hmul⟩

/-- Adding one tail-prime divisor changes the main term by `1/p`, with unchanged error. -/
theorem fourPrimeMultipleCount_error (n : ℕ) {p : ℕ} (hp : p.Prime) (hlarge : 11 < p)
    (c : Fin 16) :
    |(fourPrimeMultipleCount n p c : ℚ) - fourPrimeQ c * n / (2 * p)| ≤
      fourPrimeError c := by
  rw [fourPrimeMultipleCount_eq n hp hlarge, fourPrimeError_eq]
  have h := oddCoprimeMultiplesCount_error n
    (Nat.mul_pos (fourPrimeA_pos c) hp.pos)
    ((fourPrimeA_odd c).mul (hp.odd_of_ne_two (by omega)))
    (fourPrimeB_squarefree c) (fourPrimeB_odd c)
    ((fourPrimeAB_coprime c).mul_left (fourPrime_coprime_largePrime hp hlarge c).2)
  convert h using 2 <;> unfold fourPrimeQ <;> push_cast <;> ring

/-- Partition any further-filtered odd-vertex count by all sixteen signatures. -/
theorem fourPrime_filter_card_partition (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ c : Fin 16, ((oddUniverse n).filter (fun v => fourPrimeCode v = c ∧ P v)).card) =
      ((oddUniverse n).filter P).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (oddUniverse n).filter P) (t := Finset.univ)
    (f := fourPrimeCode) (fun v _ => Finset.mem_univ (fourPrimeCode v))
  simpa only [Finset.filter_filter, and_comm] using h.symm

theorem fourPrimeCount_partition (n : ℕ) :
    (∑ c : Fin 16, fourPrimeCount n c) = (oddUniverse n).card := by
  simpa [fourPrimeCount] using fourPrime_filter_card_partition n (fun _ => True)

#print axioms fourPrimeSet_prime
#print axioms fourPrimeSelected_subset
#print axioms fourPrimeSelected_injective
#print axioms fourPrimeA_pos
#print axioms fourPrimeA_odd
#print axioms fourPrimeB_odd
#print axioms fourPrimeB_squarefree
#print axioms fourPrimeAB_coprime
#print axioms fourPrimeError_eq
#print axioms fourPrimeQ_eq_state
#print axioms fourPrimeSmallDensity_eq_state
#print axioms fourPrimeError_sum
#print axioms fourPrimeSelected_code
#print axioms fourPrimeCode_eq_iff
#print axioms fourPrimeSmallDensity_eq_prod
#print axioms fourPrimeCount_eq
#print axioms fourPrimeCount_error
#print axioms fourPrimeCount_state_error
#print axioms fourPrime_coprime_largePrime
#print axioms fourPrimeMultipleCount_eq
#print axioms fourPrimeMultipleCount_error
#print axioms fourPrime_filter_card_partition
#print axioms fourPrimeCount_partition

end Erdos883Verified
