import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 50 through 99. -/
theorem high_cells_batch_01 : ∀ i : Fin 50, highCell (50 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_01
end Erdos883Verified
