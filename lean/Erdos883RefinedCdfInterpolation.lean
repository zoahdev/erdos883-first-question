import Erdos883RefinedCdfInterpolationCore
import Erdos883RefinedCdfCells

namespace Erdos883Verified

theorem refinedCdfBoundReal_high {t : ℝ} (hlo : 1 / 3 ≤ t) (hhi : t ≤ 3 / 4) :
    refinedCdfBoundReal t < (9 / 10) * t - 1 / 6 - 11 / 500 :=
  refinedCdfBoundReal_high_of_cells refined_high_cells hlo hhi

theorem refinedCdfBoundReal_low {β : ℝ} (hlo : 1 / 10 ≤ β) (hhi : β ≤ 201 / 100) :
    refinedCdfBoundReal (Real.sqrt ((β + 9 / 125) / 3)) < β / 3 - 1 / 400 :=
  refinedCdfBoundReal_low_of_cells refined_low_cells hlo hhi

#print axioms refinedCdfBoundReal_high
#print axioms refinedCdfBoundReal_low
end Erdos883Verified
