import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 300 through 349. -/
theorem high_cells_batch_06 : ∀ i : Fin 50, highCell (300 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_06
end Erdos883Verified
