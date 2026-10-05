import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1850 through 1874. -/
theorem low_cells_18_batch_02 : ∀ i : Fin 25, lowCell (1850 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_18_batch_02
end Erdos883Verified
