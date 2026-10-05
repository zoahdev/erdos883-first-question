import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 550 through 599. -/
theorem high_cells_batch_11 : ∀ i : Fin 50, highCell (550 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_11
end Erdos883Verified
