import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 850 through 899. -/
theorem high_cells_batch_17 : ∀ i : Fin 50, highCell (850 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_17
end Erdos883Verified
