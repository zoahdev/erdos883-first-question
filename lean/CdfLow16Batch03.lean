import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1675 through 1699. -/
theorem low_cells_16_batch_03 : ∀ i : Fin 25, lowCell (1675 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_16_batch_03
end Erdos883Verified
