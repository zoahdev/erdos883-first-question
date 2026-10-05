import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1525 through 1549. -/
theorem low_cells_15_batch_01 : ∀ i : Fin 25, lowCell (1525 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_15_batch_01
end Erdos883Verified
