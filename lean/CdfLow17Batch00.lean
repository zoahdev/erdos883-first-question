import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1700 through 1724. -/
theorem low_cells_17_batch_00 : ∀ i : Fin 25, lowCell (1700 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_17_batch_00
end Erdos883Verified
