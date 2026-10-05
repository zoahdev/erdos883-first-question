import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 150 through 199. -/
theorem high_cells_batch_03 : ∀ i : Fin 50, highCell (150 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_03
end Erdos883Verified
