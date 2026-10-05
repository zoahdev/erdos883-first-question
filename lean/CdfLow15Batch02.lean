import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1550 through 1574. -/
theorem low_cells_15_batch_02 : ∀ i : Fin 25, lowCell (1550 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_15_batch_02
end Erdos883Verified
