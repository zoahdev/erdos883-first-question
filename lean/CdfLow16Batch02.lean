import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1650 through 1674. -/
theorem low_cells_16_batch_02 : ∀ i : Fin 25, lowCell (1650 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_16_batch_02
end Erdos883Verified
