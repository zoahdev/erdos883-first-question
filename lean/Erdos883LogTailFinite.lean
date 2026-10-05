import Erdos883EulerBound
import Mathlib.Tactic.NormNum.Prime

namespace Erdos883Verified

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Rational pointwise majorant for the logarithmic first moment. -/
def logTailMajorant (p : ℕ) : ℚ :=
  1 / (p : ℚ)^2 + 1 / (2 * (p : ℚ)^2 * ((p : ℚ) - 1))

/-- The finite prime head, with non-prime inputs contributing zero. -/
def logTailHeadWeight (p : ℕ) : ℚ :=
  if p.Prime ∧ 11 < p then logTailMajorant p else 0


/-- A bounded exact rational certificate for the prime head block 0. -/
theorem logTailHead_block_0 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (0 + p)) ≤ 21202887 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 1. -/
theorem logTailHead_block_1 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (100 + p)) ≤ 1074963 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 2. -/
theorem logTailHead_block_2 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (200 + p)) ≤ 257453 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 3. -/
theorem logTailHead_block_3 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (300 + p)) ≤ 132878 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 4. -/
theorem logTailHead_block_4 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (400 + p)) ≤ 85075 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 5. -/
theorem logTailHead_block_5 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (500 + p)) ≤ 46024 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 6. -/
theorem logTailHead_block_6 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (600 + p)) ≤ 38728 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 7. -/
theorem logTailHead_block_7 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (700 + p)) ≤ 25170 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 8. -/
theorem logTailHead_block_8 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (800 + p)) ≤ 20935 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 9. -/
theorem logTailHead_block_9 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (900 + p)) ≤ 15493 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 10. -/
theorem logTailHead_block_10 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1000 + p)) ≤ 14508 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 11. -/
theorem logTailHead_block_11 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1100 + p)) ≤ 9123 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 12. -/
theorem logTailHead_block_12 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1200 + p)) ≤ 9597 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 13. -/
theorem logTailHead_block_13 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1300 + p)) ≤ 6124 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 14. -/
theorem logTailHead_block_14 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1400 + p)) ≤ 8017 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 15. -/
theorem logTailHead_block_15 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1500 + p)) ≤ 4965 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 16. -/
theorem logTailHead_block_16 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1600 + p)) ≤ 5550 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 17. -/
theorem logTailHead_block_17 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1700 + p)) ≤ 3914 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 18. -/
theorem logTailHead_block_18 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1800 + p)) ≤ 3501 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- A bounded exact rational certificate for the prime head block 19. -/
theorem logTailHead_block_19 :
    (∑ p ∈ Finset.range 100, logTailHeadWeight (1900 + p)) ≤ 3406 / 1000000000 := by
  norm_num [logTailHeadWeight, logTailMajorant, Finset.sum_range_succ]

/-- Combining the bounded certificates keeps all arithmetic kernel checked. -/
theorem logTailHead_sum_bound :
    (∑ p ∈ Finset.range 2001, logTailHeadWeight p) ≤ 22968311 / 1000000000 := by
  have h0 := logTailHead_block_0
  have h1 := logTailHead_block_1
  have h2 := logTailHead_block_2
  have h3 := logTailHead_block_3
  have h4 := logTailHead_block_4
  have h5 := logTailHead_block_5
  have h6 := logTailHead_block_6
  have h7 := logTailHead_block_7
  have h8 := logTailHead_block_8
  have h9 := logTailHead_block_9
  have h10 := logTailHead_block_10
  have h11 := logTailHead_block_11
  have h12 := logTailHead_block_12
  have h13 := logTailHead_block_13
  have h14 := logTailHead_block_14
  have h15 := logTailHead_block_15
  have h16 := logTailHead_block_16
  have h17 := logTailHead_block_17
  have h18 := logTailHead_block_18
  have h19 := logTailHead_block_19
  rw [Finset.sum_range_succ]
  rw [show logTailHeadWeight 2000 = 0 by norm_num [logTailHeadWeight], add_zero]
  rw [show 2000 = 1900 + 100 by rfl, Finset.sum_range_add]
  rw [show 1900 = 1800 + 100 by rfl, Finset.sum_range_add]
  rw [show 1800 = 1700 + 100 by rfl, Finset.sum_range_add]
  rw [show 1700 = 1600 + 100 by rfl, Finset.sum_range_add]
  rw [show 1600 = 1500 + 100 by rfl, Finset.sum_range_add]
  rw [show 1500 = 1400 + 100 by rfl, Finset.sum_range_add]
  rw [show 1400 = 1300 + 100 by rfl, Finset.sum_range_add]
  rw [show 1300 = 1200 + 100 by rfl, Finset.sum_range_add]
  rw [show 1200 = 1100 + 100 by rfl, Finset.sum_range_add]
  rw [show 1100 = 1000 + 100 by rfl, Finset.sum_range_add]
  rw [show 1000 = 900 + 100 by rfl, Finset.sum_range_add]
  rw [show 900 = 800 + 100 by rfl, Finset.sum_range_add]
  rw [show 800 = 700 + 100 by rfl, Finset.sum_range_add]
  rw [show 700 = 600 + 100 by rfl, Finset.sum_range_add]
  rw [show 600 = 500 + 100 by rfl, Finset.sum_range_add]
  rw [show 500 = 400 + 100 by rfl, Finset.sum_range_add]
  rw [show 400 = 300 + 100 by rfl, Finset.sum_range_add]
  rw [show 300 = 200 + 100 by rfl, Finset.sum_range_add]
  rw [show 200 = 100 + 100 by rfl, Finset.sum_range_add]
  simp only [Nat.zero_add] at h0
  linarith

end Erdos883Verified
