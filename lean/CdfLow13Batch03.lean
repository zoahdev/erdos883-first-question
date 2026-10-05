import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1375 through 1399. -/
theorem low_cells_13_batch_03 : ∀ i : Fin 25, lowCell (1375 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_13_batch_03
end Erdos883Verified
