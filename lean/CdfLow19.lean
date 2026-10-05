import CdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
theorem low_cells_19 : ∀ i : Fin 10, lowCell (1900 + i.val) := by
  unfold lowCell
  decide +kernel
#print axioms low_cells_19
end Erdos883Verified
