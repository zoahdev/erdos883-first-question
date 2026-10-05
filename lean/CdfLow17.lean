import CdfLow17Batch00
import CdfLow17Batch01
import CdfLow17Batch02
import CdfLow17Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- The original low-cell batch, assembled from smaller kernel-checked batches. -/
theorem low_cells_17 : ∀ i : Fin 100, lowCell (1700 + i.val) := by
  intro i
  by_cases h0 : i.val < 25
  · have h := low_cells_17_batch_00 ⟨i.val - 0, by omega⟩
    have heq : 1700 + (i.val - 0) = 1700 + i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 50
  · have h := low_cells_17_batch_01 ⟨i.val - 25, by omega⟩
    have heq : 1725 + (i.val - 25) = 1700 + i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 75
  · have h := low_cells_17_batch_02 ⟨i.val - 50, by omega⟩
    have heq : 1750 + (i.val - 50) = 1700 + i.val := by omega
    simpa only [heq] using h
  have h := low_cells_17_batch_03 ⟨i.val - 75, by omega⟩
  have heq : 1775 + (i.val - 75) = 1700 + i.val := by omega
  simpa only [heq] using h
#print axioms low_cells_17
end Erdos883Verified
