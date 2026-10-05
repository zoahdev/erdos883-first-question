import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 350 through 399. -/
theorem high_cells_batch_07 : ∀ i : Fin 50, highCell (350 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_07
end Erdos883Verified
