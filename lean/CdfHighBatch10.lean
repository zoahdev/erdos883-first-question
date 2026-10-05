import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 500 through 549. -/
theorem high_cells_batch_10 : ∀ i : Fin 50, highCell (500 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_10
end Erdos883Verified
