import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 200 through 249. -/
theorem high_cells_batch_04 : ∀ i : Fin 50, highCell (200 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_04
end Erdos883Verified
