import Erdos883RefinedCdfDefinitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified

private theorem refined_low_cells_18_first : ∀ i : Fin 50, refinedLowCell (1800 + i.val) := by
  unfold refinedLowCell
  decide +kernel

private theorem refined_low_cells_18_second : ∀ i : Fin 50, refinedLowCell (1850 + i.val) := by
  unfold refinedLowCell
  decide +kernel

theorem refined_low_cells_18 : ∀ i : Fin 100, refinedLowCell (1800 + i.val) := by
  intro i
  by_cases h : i.val < 50
  · exact refined_low_cells_18_first ⟨i.val, h⟩
  have h' := refined_low_cells_18_second ⟨i.val - 50, by omega⟩
  have heq : 1850 + (i.val - 50) = 1800 + i.val := by omega
  simpa only [heq] using h'

#print axioms refined_low_cells_18
end Erdos883Verified
