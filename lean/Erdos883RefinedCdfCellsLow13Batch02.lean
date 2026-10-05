import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked refined low CDF cells 1350 through 1374. -/
theorem refined_low_cells_13_batch_02 : ∀ i : Fin 25, refinedLowCell (1350 + i.val) := by
  unfold refinedLowCell
  decide +kernel
#print axioms refined_low_cells_13_batch_02
end Erdos883Verified
