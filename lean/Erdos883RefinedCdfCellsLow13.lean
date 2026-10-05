import Erdos883RefinedCdfCellsLow13Batch00
import Erdos883RefinedCdfCellsLow13Batch01
import Erdos883RefinedCdfCellsLow13Batch02
import Erdos883RefinedCdfCellsLow13Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- The original refined low-cell statement, assembled from bounded kernel-checked batches. -/
theorem refined_low_cells_13 : ∀ i : Fin 100, refinedLowCell (1300 + i.val) := by
  intro i
  by_cases h0 : i.val < 25
  · have h := refined_low_cells_13_batch_00 ⟨i.val - 0, by omega⟩
    have heq : 1300 + (i.val - 0) = 1300 + i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 50
  · have h := refined_low_cells_13_batch_01 ⟨i.val - 25, by omega⟩
    have heq : 1325 + (i.val - 25) = 1300 + i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 75
  · have h := refined_low_cells_13_batch_02 ⟨i.val - 50, by omega⟩
    have heq : 1350 + (i.val - 50) = 1300 + i.val := by omega
    simpa only [heq] using h
  have h := refined_low_cells_13_batch_03 ⟨i.val - 75, by omega⟩
  have heq : 1375 + (i.val - 75) = 1300 + i.val := by omega
  simpa only [heq] using h
#print axioms refined_low_cells_13
end Erdos883Verified
