import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

theorem refined_high_cells_01 : ∀ i : Fin 100, refinedHighCell (100 + i.val) := by
  unfold refinedHighCell
  decide +kernel

#print axioms refined_high_cells_01
end Erdos883Verified
