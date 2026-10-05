import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked refined low CDF cells 1300 through 1324. -/
theorem refined_low_cells_13_batch_00 : ∀ i : Fin 25, refinedLowCell (1300 + i.val) := by
  unfold refinedLowCell
  decide +kernel
#print axioms refined_low_cells_13_batch_00
end Erdos883Verified
