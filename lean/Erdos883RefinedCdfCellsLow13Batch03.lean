import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked refined low CDF cells 1375 through 1399. -/
theorem refined_low_cells_13_batch_03 : ∀ i : Fin 25, refinedLowCell (1375 + i.val) := by
  unfold refinedLowCell
  decide +kernel
#print axioms refined_low_cells_13_batch_03
end Erdos883Verified
