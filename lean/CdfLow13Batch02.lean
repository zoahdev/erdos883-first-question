import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1350 through 1374. -/
theorem low_cells_13_batch_02 : ∀ i : Fin 25, lowCell (1350 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_13_batch_02
end Erdos883Verified
