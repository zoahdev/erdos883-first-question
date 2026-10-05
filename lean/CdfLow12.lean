import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
theorem low_cells_12 : ∀ i : Fin 100, lowCell (1200 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_12
end Erdos883Verified
