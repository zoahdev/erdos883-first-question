import CdfLow16Batch00
import CdfLow16Batch01
import CdfLow16Batch02
import CdfLow16Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- The original low-cell batch, assembled from smaller kernel-checked batches. -/
theorem low_cells_16 : ∀ i : Fin 100, lowCell (1600 + i.val) := by
  intro i
  by_cases h0 : i.val < 25
  · have h := low_cells_16_batch_00 ⟨i.val - 0, by omega⟩
    have heq : 1600 + (i.val - 0) = 1600 + i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 50
  · have h := low_cells_16_batch_01 ⟨i.val - 25, by omega⟩
    have heq : 1625 + (i.val - 25) = 1600 + i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 75
  · have h := low_cells_16_batch_02 ⟨i.val - 50, by omega⟩
    have heq : 1650 + (i.val - 50) = 1600 + i.val := by omega
    simpa only [heq] using h
  have h := low_cells_16_batch_03 ⟨i.val - 75, by omega⟩
  have heq : 1675 + (i.val - 75) = 1600 + i.val := by omega
  simpa only [heq] using h
#print axioms low_cells_16
end Erdos883Verified
