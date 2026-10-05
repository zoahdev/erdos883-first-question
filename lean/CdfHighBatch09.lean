import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 450 through 499. -/
theorem high_cells_batch_09 : ∀ i : Fin 50, highCell (450 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_09
end Erdos883Verified
