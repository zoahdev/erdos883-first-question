import Erdos883TotientMoment
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos883Verified

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A purely algebraic upper bound for a finite product of small positive increments. -/
theorem prod_one_add_le_reciprocal {ι : Type*} (s : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : ∑ i ∈ s, x i < 1) :
    (∏ i ∈ s, (1 + x i)) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  classical
  have hmul : (∏ i ∈ s, (1 + x i)) * (1 - ∑ i ∈ s, x i) ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hs
      have hxa := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
      have hprod : 0 ≤ ∏ i ∈ s, (1 + x i) :=
        Finset.prod_nonneg fun i hi => by linarith [hxs i hi]
      have hih := ih hxs (by linarith)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      nlinarith [mul_nonneg (mul_nonneg hprod hxa) (add_nonneg hxa hsum)]
  exact (le_div_iff₀ (sub_pos.mpr hs)).mpr hmul

/-- Sixth powers near one have a convenient rational linear majorant. -/
theorem one_add_pow_six_le {y : ℚ} (hy : 0 ≤ y) (hy' : y ≤ 1 / 200) :
    (1 + y)^6 ≤ 1 + 7*y := by
  have h := prod_one_add_le_reciprocal (Finset.range 6) (fun _ => y)
    (fun _ _ => hy) (by simpa using (show (6 : ℚ)*y < 1 by linarith))
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const,
    nsmul_eq_mul] at h
  apply h.trans
  apply (div_le_iff₀ (show (0 : ℚ) < 1 - 6*y by linarith)).mpr
  nlinarith [mul_nonneg hy (show (0 : ℚ) ≤ 1 - 42*y by linarith)]

/-- The large-prime contribution is bounded by a telescoping reciprocal. -/
theorem totientMomentWeight_le {p : ℕ} (hp : 200 < p) :
    totientMomentWeight p ≤ 7 / ((p : ℚ)-1) := by
  have hpq : (200 : ℚ) < p := by exact_mod_cast hp
  have hpos : (0 : ℚ) < p - 1 := by linarith
  have hy : (0 : ℚ) ≤ 1 / (p-1) := le_of_lt (div_pos (by norm_num) hpos)
  have hy' : (1 : ℚ)/(p-1) ≤ 1/200 := by
    apply (div_le_div_iff₀ hpos (by norm_num)).mpr
    have hh : (201 : ℚ) ≤ p := by exact_mod_cast hp
    linarith
  have h := one_add_pow_six_le hy hy'
  have heq : (p : ℚ)/(p-1) = 1+1/(p-1) := by field_simp; ring
  unfold totientMomentWeight
  rw [heq]
  calc
    _ ≤ 7 * (1 / ((p : ℚ)-1)) := by linarith
    _ = _ := by ring

/-- The comparison series is finite and telescopes exactly. -/
theorem reciprocal_tail_interval (n : ℕ) :
    (∑ p ∈ Finset.Icc 201 (200+n), (1 : ℚ) / (p * (p-1))) =
      1/200 - 1/(200+n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    have hn : (200 : ℚ) + n ≠ 0 := by positivity
    have hn' : (200 : ℚ) + n + 1 ≠ 0 := by positivity
    simp only [add_sub_cancel_right]
    field_simp [hn, hn']
    <;> ring

/-- An arbitrary finite subset of the tail has at most the full telescoping mass. -/
theorem reciprocal_tail_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, 200 < p) :
    (∑ p ∈ P, (1 : ℚ) / (p * (p-1))) ≤ 1/200 := by
  have hsub : P ⊆ Finset.Icc 201 (200 + P.sup id) := by
    intro p hp
    have hle : p ≤ P.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_Icc.mpr ⟨by have := hP p hp; omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ Finset.Icc 201 (200 + P.sup id), (1 : ℚ)/(p*(p-1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hpq : (201 : ℚ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
      apply div_nonneg (by norm_num)
      exact mul_nonneg (by linarith) (by linarith)
    _ = 1/200 - 1/(200+P.sup id) := reciprocal_tail_interval _
    _ ≤ _ := by
      have h : (0 : ℚ) ≤ 1/(200 + P.sup id) := by positivity
      linarith

/-- The sum of all large-prime Euler increments is uniformly small. -/
theorem totientEuler_tail_sum_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, 200 < p) :
    (∑ p ∈ P, totientMomentWeight p / p) ≤ 7/200 := by
  calc
    _ ≤ ∑ p ∈ P, (7 : ℚ)/(p*(p-1)) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        _ ≤ (7 / ((p : ℚ)-1)) / p :=
          div_le_div_of_nonneg_right (totientMomentWeight_le (hP p hp)) (Nat.cast_nonneg _)
        _ = _ := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = 7 * ∑ p ∈ P, (1 : ℚ)/(p*(p-1)) := by rw [Finset.mul_sum]; congr 1; ext p; ring
    _ ≤ 7 * (1/200) := mul_le_mul_of_nonneg_left (reciprocal_tail_sum_le P hP) (by norm_num)
    _ = _ := by norm_num

/-- The entire tail costs at most the rational factor `200/193`. -/
theorem totientEuler_tail_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 200 < p) :
    totientEulerProduct P ≤ 200/193 := by
  have hs := totientEuler_tail_sum_le P (fun p hp => (hP p hp).2)
  have hs' : (∑ p ∈ P, totientMomentWeight p / p) < 1 := by linarith
  calc
    _ ≤ 1 / (1 - ∑ p ∈ P, totientMomentWeight p / p) :=
      prod_one_add_le_reciprocal P (fun p => totientMomentWeight p/p)
        (fun p hp => div_nonneg (totientMomentWeight_nonneg (hP p hp).1) (Nat.cast_nonneg _)) hs'
    _ ≤ 200/193 := by
      apply (div_le_iff₀ (sub_pos.mpr hs')).mpr
      linarith

/-- The complete finite head of odd primes at most 200. -/
def totientEulerHead : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
   71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
   149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199}

/-- A kernel-checked, bounded primality enumeration. -/
theorem totientEulerHead_complete :
    ∀ p ∈ Finset.range 201, p.Prime → 3 ≤ p → p ∈ totientEulerHead := by
  decide

/-- Exact rational arithmetic certifies the head and tail constant. -/
theorem totientEulerHead_bound :
    totientEulerProduct totientEulerHead * (200/193) < 11 := by
  norm_num [totientEulerProduct, totientEulerHead, totientMomentWeight]

/-- Every listed head element really is prime. -/
theorem totientEulerHead_prime : ∀ p ∈ totientEulerHead, p.Prime := by decide

/-- Uniform finite sixth-moment Euler bound over any set of odd primes. -/
theorem totientEulerProduct_lt_eleven (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) :
    totientEulerProduct P < 11 := by
  have hfactor : ∀ p, p.Prime → 1 ≤ 1 + totientMomentWeight p / p := by
    intro p hp
    have h := div_nonneg (totientMomentWeight_nonneg hp) (Nat.cast_nonneg p : (0 : ℚ) ≤ p)
    linarith
  have hhead : totientEulerProduct (P ∩ totientEulerHead) ≤
      totientEulerProduct totientEulerHead := by
    apply Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
    · intro p hp
      exact le_trans (by norm_num) (hfactor p (hP p (Finset.mem_inter.mp hp).1).1)
    · intro p hp _
      exact hfactor p (totientEulerHead_prime p hp)
  have htail : totientEulerProduct (P \ totientEulerHead) ≤ 200/193 := by
    apply totientEuler_tail_le
    intro p hp
    obtain ⟨hpP, hphead⟩ := Finset.mem_sdiff.mp hp
    refine ⟨(hP p hpP).1, ?_⟩
    by_contra hn
    have hple : p ≤ 200 := by omega
    exact hphead (totientEulerHead_complete p (Finset.mem_range.mpr (by omega))
      (hP p hpP).1 (hP p hpP).2)
  calc
    _ = totientEulerProduct (P ∩ totientEulerHead) *
        totientEulerProduct (P \ totientEulerHead) :=
      (Finset.prod_inter_mul_prod_sdiff P totientEulerHead
        (fun p => 1 + totientMomentWeight p / p)).symm
    _ ≤ totientEulerProduct totientEulerHead * (200/193) := by
      apply mul_le_mul hhead htail
      · apply Finset.prod_nonneg
        intro p hp
        exact le_trans (by norm_num) (hfactor p (hP p (Finset.mem_sdiff.mp hp).1).1)
      · apply Finset.prod_nonneg
        intro p hp
        exact le_trans (by norm_num) (hfactor p (totientEulerHead_prime p hp))
    _ < 11 := totientEulerHead_bound

/-- The canonical odd-prime support satisfies the same absolute constant. -/
theorem oddPrimeSupport_euler_lt_eleven (n : ℕ) :
    totientEulerProduct (oddPrimeSupport n) < 11 :=
  totientEulerProduct_lt_eleven _ (fun _ hp =>
    ⟨oddPrimeSupport_prime hp, oddPrimeSupport_three_le hp⟩)

/-- Unconditional rational-threshold sixth-moment CDF estimate. -/
theorem odd_totient_cdf_lt_twenty_two_uniform {n : ℕ} (hn : 0 < n)
    {t : ℚ} (ht : 0 < t) :
    (2 / (n : ℚ)) * (((oddUniverse n).filter
      (fun v => totientDensity v < t)).card : ℚ) < 22 * t ^ 6 :=
  odd_totient_cdf_lt_twenty_two hn (oddPrimeSupport_euler_lt_eleven n) ht

/-- Unconditional real-threshold sixth-moment CDF estimate. -/
theorem odd_totient_cdf_lt_twenty_two_real_uniform {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) :
    (2 / (n : ℝ)) * (((oddUniverse n).filter
      (fun v => (totientDensity v : ℝ) < t)).card : ℝ) < 22 * t ^ 6 :=
  odd_totient_cdf_lt_twenty_two_real hn (oddPrimeSupport_euler_lt_eleven n) ht

end Erdos883Verified

#print axioms Erdos883Verified.totientEulerProduct_lt_eleven
#print axioms Erdos883Verified.oddPrimeSupport_euler_lt_eleven
#print axioms Erdos883Verified.odd_totient_cdf_lt_twenty_two_real_uniform
