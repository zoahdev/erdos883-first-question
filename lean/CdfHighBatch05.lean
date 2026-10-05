import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked high CDF cells 250 through 299. -/
theorem high_cells_batch_05 : ∀ i : Fin 50, highCell (250 + i.val) := by
  unfold highCell
  decide +kernel
#print axioms high_cells_batch_05
end Erdos883Verified
