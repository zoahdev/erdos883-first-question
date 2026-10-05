import Erdos883RefinedCdfEnvelope
import Erdos883RefinedCdfInterpolation

namespace Erdos883Verified

/-- The actual finite odd-totient CDF has the refined high-range margin after 200000. -/
theorem totientCdf_refined_high {n : ℕ} {t : ℝ}
    (hn : 200000 ≤ n) (hlo : 1 / 3 ≤ t) (hhi : t ≤ 3 / 4) :
    totientCdf n t < (9 / 10) * t - 1 / 6 - 11 / 500 := by
  exact (totientCdf_le_refined_envelope hn (by linarith : 0 < t)).trans_lt
    (refinedCdfBoundReal_high hlo hhi)

/-- The actual finite odd-totient CDF has the refined square-root margin after 200000. -/
theorem totientCdf_refined_low {n : ℕ} {β : ℝ}
    (hn : 200000 ≤ n) (hlo : 1 / 10 ≤ β) (hhi : β ≤ 201 / 100) :
    totientCdf n (Real.sqrt ((β + 9 / 125) / 3)) < β / 3 - 1 / 400 := by
  have ht : 0 < Real.sqrt ((β + 9 / 125) / 3) := Real.sqrt_pos.mpr (by linarith)
  exact (totientCdf_le_refined_envelope hn ht).trans_lt
    (refinedCdfBoundReal_low hlo hhi)

#print axioms totientCdf_refined_high
#print axioms totientCdf_refined_low
end Erdos883Verified
