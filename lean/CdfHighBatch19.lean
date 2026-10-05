import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 950 through 999. -/
theorem high_cells_batch_19 : ∀ i : Fin 50, highCell (950 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_19
end Erdos883Verified
