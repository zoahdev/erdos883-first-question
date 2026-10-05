import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1575 through 1599. -/
theorem low_cells_15_batch_03 : ∀ i : Fin 25, lowCell (1575 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_15_batch_03
end Erdos883Verified
