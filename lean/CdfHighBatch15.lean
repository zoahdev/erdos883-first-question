import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 750 through 799. -/
theorem high_cells_batch_15 : ∀ i : Fin 50, highCell (750 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_15
end Erdos883Verified
