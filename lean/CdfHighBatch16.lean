import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 800 through 849. -/
theorem high_cells_batch_16 : ∀ i : Fin 50, highCell (800 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_16
end Erdos883Verified
