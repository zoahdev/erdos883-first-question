import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

theorem refined_low_cells_02 : ∀ i : Fin 100, refinedLowCell (200 + i.val) := by
  unfold refinedLowCell
  decide +kernel

#print axioms refined_low_cells_02
end Erdos883Verified
