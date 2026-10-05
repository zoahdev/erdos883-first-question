import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- Kernel-checked low CDF cells 1775 through 1799. -/
theorem low_cells_17_batch_03 : ∀ i : Fin 25, lowCell (1775 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_17_batch_03
end Erdos883Verified
