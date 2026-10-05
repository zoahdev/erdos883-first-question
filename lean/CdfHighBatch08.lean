import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 400 through 449. -/
theorem high_cells_batch_08 : ∀ i : Fin 50, highCell (400 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_08
end Erdos883Verified
