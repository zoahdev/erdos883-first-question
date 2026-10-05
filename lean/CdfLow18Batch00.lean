import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1800 through 1824. -/
theorem low_cells_18_batch_00 : ∀ i : Fin 25, lowCell (1800 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_18_batch_00
end Erdos883Verified
