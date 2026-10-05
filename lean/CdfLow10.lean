import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
theorem low_cells_10 : ∀ i : Fin 100, lowCell (1000 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_10
end Erdos883Verified
