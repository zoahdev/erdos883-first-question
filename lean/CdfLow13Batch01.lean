import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1325 through 1349. -/
theorem low_cells_13_batch_01 : ∀ i : Fin 25, lowCell (1325 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_13_batch_01
end Erdos883Verified
