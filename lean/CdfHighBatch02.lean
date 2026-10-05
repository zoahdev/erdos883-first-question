import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 100 through 149. -/
theorem high_cells_batch_02 : ∀ i : Fin 50, highCell (100 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_02
end Erdos883Verified
