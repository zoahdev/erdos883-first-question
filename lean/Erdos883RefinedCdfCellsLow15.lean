import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

private theorem refined_low_cells_15_first : ∀ i : Fin 50, refinedLowCell (1500 + i.val) := by
  unfold refinedLowCell
  decide +kernel

private theorem refined_low_cells_15_second : ∀ i : Fin 50, refinedLowCell (1550 + i.val) := by
  unfold refinedLowCell
  decide +kernel

theorem refined_low_cells_15 : ∀ i : Fin 100, refinedLowCell (1500 + i.val) := by
  intro i
  by_cases h : i.val < 50
  · exact refined_low_cells_15_first ⟨i.val, h⟩
  have h' := refined_low_cells_15_second ⟨i.val - 50, by omega⟩
  have heq : 1550 + (i.val - 50) = 1500 + i.val := by omega
  simpa only [heq] using h'

#print axioms refined_low_cells_15
end Erdos883Verified
