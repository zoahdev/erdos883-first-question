import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 650 through 699. -/
theorem high_cells_batch_13 : ∀ i : Fin 50, highCell (650 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_13
end Erdos883Verified
