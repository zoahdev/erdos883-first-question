import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 700 through 749. -/
theorem high_cells_batch_14 : ∀ i : Fin 50, highCell (700 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_14
end Erdos883Verified
