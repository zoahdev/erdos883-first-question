import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 900 through 949. -/
theorem high_cells_batch_18 : ∀ i : Fin 50, highCell (900 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_18
end Erdos883Verified
