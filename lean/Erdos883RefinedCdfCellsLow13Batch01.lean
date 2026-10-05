import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked refined low CDF cells 1325 through 1349. -/
theorem refined_low_cells_13_batch_01 : ∀ i : Fin 25, refinedLowCell (1325 + i.val) := by
  unfold refinedLowCell
  decide +kernel
#print axioms refined_low_cells_13_batch_01
end Erdos883Verified
