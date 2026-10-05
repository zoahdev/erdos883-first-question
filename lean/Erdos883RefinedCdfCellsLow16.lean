import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

private theorem refined_low_cells_16_first : ∀ i : Fin 50, refinedLowCell (1600 + i.val) := by
  unfold refinedLowCell
  decide +kernel

private theorem refined_low_cells_16_second : ∀ i : Fin 50, refinedLowCell (1650 + i.val) := by
  unfold refinedLowCell
  decide +kernel

theorem refined_low_cells_16 : ∀ i : Fin 100, refinedLowCell (1600 + i.val) := by
  intro i
  by_cases h : i.val < 50
  · exact refined_low_cells_16_first ⟨i.val, h⟩
  have h' := refined_low_cells_16_second ⟨i.val - 50, by omega⟩
  have heq : 1650 + (i.val - 50) = 1600 + i.val := by omega
  simpa only [heq] using h'

#print axioms refined_low_cells_16
end Erdos883Verified
