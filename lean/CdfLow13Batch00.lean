import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1300 through 1324. -/
theorem low_cells_13_batch_00 : ∀ i : Fin 25, lowCell (1300 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_13_batch_00
end Erdos883Verified
