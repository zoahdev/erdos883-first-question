import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 0 through 49. -/
theorem high_cells_batch_00 : ∀ i : Fin 50, highCell (0 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_00
end Erdos883Verified
