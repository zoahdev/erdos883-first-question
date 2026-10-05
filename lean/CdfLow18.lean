import CdfLow18Batch00
import CdfLow18Batch01
import CdfLow18Batch02
import CdfLow18Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos883Verified
/-- The original low-cell batch, assembled from smaller kernel-checked batches. -/
theorem low_cells_18 : ∀ i : Fin 100, lowCell (1800 + i.val) := by
  intro i
  by_cases h0 : i.val < 25
  · have h := low_cells_18_batch_00 ⟨i.val - 0, by omega⟩
    have heq : 1800 + (i.val - 0) = 1800 + i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 50
  · have h := low_cells_18_batch_01 ⟨i.val - 25, by omega⟩
    have heq : 1825 + (i.val - 25) = 1800 + i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 75
  · have h := low_cells_18_batch_02 ⟨i.val - 50, by omega⟩
    have heq : 1850 + (i.val - 50) = 1800 + i.val := by omega
    simpa only [heq] using h
  have h := low_cells_18_batch_03 ⟨i.val - 75, by omega⟩
  have heq : 1875 + (i.val - 75) = 1800 + i.val := by omega
  simpa only [heq] using h
#print axioms low_cells_18
end Erdos883Verified
