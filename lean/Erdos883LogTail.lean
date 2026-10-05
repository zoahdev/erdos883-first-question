import Erdos883LogTailFinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos883Verified

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The logarithmic loss attached to a prime Euler factor. -/
noncomputable def logTailLambda (p : ℕ) : ℝ :=
  Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- Euler factors at integers greater than one have nonnegative logarithm. -/
theorem logTailLambda_nonneg {p : ℕ} (hp : 1 < p) :
    0 ≤ logTailLambda p := by
  apply Real.log_nonneg
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
  linarith

/-- A symmetric rational upper bound for logarithms on `[1,∞)`. -/
theorem log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ (y - 1 / y) / 2 := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hy)
  simpa only [Real.sinh_eq, Real.exp_log hypos, Real.exp_neg,
    one_div] using h

/-- The finite-head majorant has a quadratic main term and a cubic correction. -/
theorem logTailLambda_div_le_majorant {p : ℕ} (hp : 1 < p) :
    logTailLambda p / p ≤ (logTailMajorant p : ℝ) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hy : (1 : ℝ) ≤ p / (p - 1) := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith
  have h := div_le_div_of_nonneg_right (log_le_half_sub_inv hy)
    (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  unfold logTailLambda logTailMajorant
  push_cast
  calc
    _ ≤ (((p : ℝ) / (p - 1) - 1 / ((p : ℝ) / (p - 1))) / 2) / p := h
    _ = _ := by field_simp [hp0, hp1]; ring

/-- A looser majorant used only beyond the finite head. -/
theorem logTailLambda_div_le_reciprocal {p : ℕ} (hp : 1 < p) :
    logTailLambda p / p ≤ (1 : ℝ) / (p * (p - 1)) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h := Real.log_le_sub_one_of_pos
    (div_pos (by linarith : (0 : ℝ) < p) (by linarith : (0 : ℝ) < p - 1))
  calc
    _ ≤ ((p : ℝ)/(p-1)-1)/p :=
      div_le_div_of_nonneg_right h (Nat.cast_nonneg p)
    _ = _ := by field_simp; ring

/-- The reciprocal comparison tail telescopes, with an arbitrary positive cutoff. -/
theorem logTail_reciprocal_interval (m n : ℕ) (hm : 0 < m) :
    (∑ p ∈ Finset.Icc (m+1) (m+n), (1 : ℝ) / (p * (p-1))) =
      1/(m : ℝ) - 1/(m+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hn : (m : ℝ) + n ≠ 0 := by positivity
    have hn' : (m : ℝ) + n + 1 ≠ 0 := by positivity
    simp only [add_sub_cancel_right]
    field_simp [hn, hn']
    ring

/-- Any finite set beyond the cutoff costs at most its reciprocal. -/
theorem logTail_reciprocal_sum_le (P : Finset ℕ) {m : ℕ} (hm : 0 < m)
    (hP : ∀ p ∈ P, m < p) :
    (∑ p ∈ P, (1 : ℝ) / (p * (p-1))) ≤ 1/(m : ℝ) := by
  have hsub : P ⊆ Finset.Icc (m+1) (m + P.sup id) := by
    intro p hp
    have hle : p ≤ P.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_Icc.mpr ⟨by have := hP p hp; omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ Finset.Icc (m+1) (m + P.sup id), (1 : ℝ)/(p*(p-1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hpn : 1 ≤ p := by have := (Finset.mem_Icc.mp hp).1; omega
      have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hpn
      apply div_nonneg (by norm_num)
      exact mul_nonneg (by linarith) (by linarith)
    _ = 1/(m : ℝ) - 1/(m+P.sup id) := logTail_reciprocal_interval _ _ hm
    _ ≤ _ := by
      have h : (0 : ℝ) ≤ 1/((m : ℝ) + P.sup id) := by positivity
      linarith

/-- The rational majorant is nonnegative throughout the prime head. -/
theorem logTailMajorant_nonneg {p : ℕ} (hp : 1 < p) :
    0 ≤ logTailMajorant p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  unfold logTailMajorant
  positivity

/-- The prime-head weight is nonnegative on every natural input. -/
theorem logTailHeadWeight_nonneg (p : ℕ) : 0 ≤ logTailHeadWeight p := by
  unfold logTailHeadWeight
  split_ifs with hp
  · exact logTailMajorant_nonneg (by omega)
  · exact le_rfl

/-- A uniform first-moment constant for any finite collection of primes above eleven. -/
theorem logTailLambda_sum_lt (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 11 < p) :
    (∑ p ∈ P, logTailLambda p / p) < (47 : ℝ) / 2000 := by
  have hhead : (∑ p ∈ P ∩ Finset.range 2001, logTailLambda p / p) ≤
      (22968311 : ℝ) / 1000000000 := by
    calc
      _ ≤ ∑ p ∈ P ∩ Finset.range 2001, (logTailHeadWeight p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := hP p (Finset.mem_inter.mp hp).1
        simpa only [logTailHeadWeight, if_pos hpp] using
          (logTailLambda_div_le_majorant (p := p) (by omega))
      _ ≤ ∑ p ∈ Finset.range 2001, (logTailHeadWeight p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro p _ _
        exact_mod_cast logTailHeadWeight_nonneg p
      _ ≤ _ := by
        have h := (Rat.cast_le (K := ℝ)).mpr logTailHead_sum_bound
        push_cast at h
        exact h
  have htail : (∑ p ∈ P \ Finset.range 2001, logTailLambda p / p) ≤
      (1 : ℝ) / 2000 := by
    calc
      _ ≤ ∑ p ∈ P \ Finset.range 2001, (1 : ℝ) / (p * (p - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := hP p (Finset.mem_sdiff.mp hp).1
        exact logTailLambda_div_le_reciprocal (by omega)
      _ ≤ _ := by
        apply logTail_reciprocal_sum_le _ (by norm_num : 0 < (2000 : ℕ))
        intro p hp
        have hnot := (Finset.mem_sdiff.mp hp).2
        have hnot' : ¬ p < 2001 := by simpa only [Finset.mem_range] using hnot
        omega
  have hsplit := Finset.sum_inter_add_sum_sdiff P (Finset.range 2001)
    (fun p => logTailLambda p / p)
  linarith

/-- Pairing adjacent odd integers gives a logarithmic telescoping majorant. -/
theorem logTailLambda_le_half_log_gap {p : ℕ} (hp : 2 < p) :
    logTailLambda p ≤ (Real.log (p : ℝ) - Real.log ((p : ℝ) - 2)) / 2 := by
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hypos : (0 : ℝ) < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hsq : ((p : ℝ) / (p - 1)) ^ 2 ≤ (p : ℝ) / (p - 2) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hp1)
      (by linarith : (0 : ℝ) < p - 2)).mpr
    nlinarith
  have hlog := Real.log_le_log (pow_pos hypos 2) hsq
  rw [Real.log_pow, Real.log_div hp0 hp2] at hlog
  unfold logTailLambda
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- The sum over an initial segment of odd integers telescopes. -/
theorem logTailLambda_odd_interval (m : ℕ) (hm : 6 ≤ m) :
    (∑ k ∈ Finset.Icc 6 m, logTailLambda (2*k+1)) ≤
      (Real.log (2*(m : ℝ)+1) - Real.log 11) / 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    convert (logTailLambda_le_half_log_gap (p := 13) (by norm_num)) using 1 <;> norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := logTailLambda_le_half_log_gap (p := 2*(m+1)+1) (by omega)
    have heq : ((2*(m+1)+1 : ℕ) : ℝ) - 2 = 2*(m : ℝ)+1 := by push_cast; ring
    rw [heq] at h
    push_cast at h ⊢
    linarith

/-- A uniform logarithmic bound for the unweighted finite-prime loss. -/
theorem logTailLambda_sum_le_log (P : Finset ℕ) {n : ℕ} (hn : 13 ≤ n)
    (hP : ∀ p ∈ P, p.Prime ∧ 11 < p ∧ p ≤ n) :
    (∑ p ∈ P, logTailLambda p) ≤ (1 / 2 : ℝ) * Real.log ((n : ℝ) / 10) := by
  have hodd : ∀ p ∈ P, 2*(p/2)+1 = p := by
    intro p hp
    have hp' := hP p hp
    have ho := Nat.odd_iff.mp (hp'.1.odd_of_ne_two (by omega))
    omega
  have hinj : ∀ p ∈ P, ∀ q ∈ P, p / 2 = q / 2 → p = q := by
    intro p hp q hq hpq
    have hp' := hodd p hp
    have hq' := hodd q hq
    omega
  have hsub : P.image (fun p => p/2) ⊆ Finset.Icc 6 (n/2) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hp' := hP p hp
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · exact Nat.div_le_div_right hp'.2.2
  have hsum : (∑ p ∈ P, logTailLambda p) =
      ∑ k ∈ P.image (fun p => p/2), logTailLambda (2*k+1) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hodd p hp]
  have hn' : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have hquot : (2*((n/2 : ℕ) : ℝ)+1) / 11 ≤ (n : ℝ) / 10 := by
    have hnat : 2*(n/2) ≤ n := by omega
    have hreal : (2 : ℝ)*((n/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnat
    nlinarith
  have hlog := Real.log_le_log (by positivity :
    (0 : ℝ) < (2*((n/2 : ℕ) : ℝ)+1) / 11) hquot
  rw [Real.log_div (by positivity : (2*((n/2 : ℕ) : ℝ)+1) ≠ 0)
    (by norm_num : (11 : ℝ) ≠ 0)] at hlog
  calc
    _ = ∑ k ∈ P.image (fun p => p/2), logTailLambda (2*k+1) := hsum
    _ ≤ ∑ k ∈ Finset.Icc 6 (n/2), logTailLambda (2*k+1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk _
      have hk' := (Finset.mem_Icc.mp hk).1
      exact logTailLambda_nonneg (by omega)
    _ ≤ (Real.log (2*((n/2 : ℕ) : ℝ)+1) - Real.log 11) / 2 :=
      logTailLambda_odd_interval _ (by omega)
    _ ≤ _ := by linarith

end Erdos883Verified

#print axioms Erdos883Verified.logTailLambda_sum_lt

#print axioms Erdos883Verified.logTailLambda_sum_le_log
