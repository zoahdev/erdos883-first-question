import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1600 through 1624. -/
theorem low_cells_16_batch_00 : ∀ i : Fin 25, lowCell (1600 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_16_batch_00
end Erdos883Verified
