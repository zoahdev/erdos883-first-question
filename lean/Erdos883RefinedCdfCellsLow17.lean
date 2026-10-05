import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

private theorem refined_low_cells_17_first : ∀ i : Fin 50, refinedLowCell (1700 + i.val) := by
  unfold refinedLowCell
  decide +kernel

private theorem refined_low_cells_17_second : ∀ i : Fin 50, refinedLowCell (1750 + i.val) := by
  unfold refinedLowCell
  decide +kernel

theorem refined_low_cells_17 : ∀ i : Fin 100, refinedLowCell (1700 + i.val) := by
  intro i
  by_cases h : i.val < 50
  · exact refined_low_cells_17_first ⟨i.val, h⟩
  have h' := refined_low_cells_17_second ⟨i.val - 50, by omega⟩
  have heq : 1750 + (i.val - 50) = 1700 + i.val := by omega
  simpa only [heq] using h'

#print axioms refined_low_cells_17
end Erdos883Verified
