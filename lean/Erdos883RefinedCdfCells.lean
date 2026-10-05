import Erdos883RefinedCdfCellsHigh00
import Erdos883RefinedCdfCellsHigh01
import Erdos883RefinedCdfCellsHigh02
import Erdos883RefinedCdfCellsHigh03
import Erdos883RefinedCdfCellsHigh04
import Erdos883RefinedCdfCellsHigh05
import Erdos883RefinedCdfCellsHigh06
import Erdos883RefinedCdfCellsHigh07
import Erdos883RefinedCdfCellsHigh08
import Erdos883RefinedCdfCellsHigh09
import Erdos883RefinedCdfCellsLow00
import Erdos883RefinedCdfCellsLow01
import Erdos883RefinedCdfCellsLow02
import Erdos883RefinedCdfCellsLow03
import Erdos883RefinedCdfCellsLow04
import Erdos883RefinedCdfCellsLow05
import Erdos883RefinedCdfCellsLow06
import Erdos883RefinedCdfCellsLow07
import Erdos883RefinedCdfCellsLow08
import Erdos883RefinedCdfCellsLow09
import Erdos883RefinedCdfCellsLow10
import Erdos883RefinedCdfCellsLow11
import Erdos883RefinedCdfCellsLow12
import Erdos883RefinedCdfCellsLow13
import Erdos883RefinedCdfCellsLow14
import Erdos883RefinedCdfCellsLow15
import Erdos883RefinedCdfCellsLow16
import Erdos883RefinedCdfCellsLow17
import Erdos883RefinedCdfCellsLow18
import Erdos883RefinedCdfCellsLow19

namespace Erdos883Verified

theorem refined_high_cells : ∀ i : Fin 1000, refinedHighCell i.val := by
  intro i
  by_cases h0 : i.val < 100
  · have h := refined_high_cells_00 ⟨i.val - 0, by omega⟩
    have heq : 0 + (i.val - 0) = i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 200
  · have h := refined_high_cells_01 ⟨i.val - 100, by omega⟩
    have heq : 100 + (i.val - 100) = i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 300
  · have h := refined_high_cells_02 ⟨i.val - 200, by omega⟩
    have heq : 200 + (i.val - 200) = i.val := by omega
    simpa only [heq] using h
  by_cases h3 : i.val < 400
  · have h := refined_high_cells_03 ⟨i.val - 300, by omega⟩
    have heq : 300 + (i.val - 300) = i.val := by omega
    simpa only [heq] using h
  by_cases h4 : i.val < 500
  · have h := refined_high_cells_04 ⟨i.val - 400, by omega⟩
    have heq : 400 + (i.val - 400) = i.val := by omega
    simpa only [heq] using h
  by_cases h5 : i.val < 600
  · have h := refined_high_cells_05 ⟨i.val - 500, by omega⟩
    have heq : 500 + (i.val - 500) = i.val := by omega
    simpa only [heq] using h
  by_cases h6 : i.val < 700
  · have h := refined_high_cells_06 ⟨i.val - 600, by omega⟩
    have heq : 600 + (i.val - 600) = i.val := by omega
    simpa only [heq] using h
  by_cases h7 : i.val < 800
  · have h := refined_high_cells_07 ⟨i.val - 700, by omega⟩
    have heq : 700 + (i.val - 700) = i.val := by omega
    simpa only [heq] using h
  by_cases h8 : i.val < 900
  · have h := refined_high_cells_08 ⟨i.val - 800, by omega⟩
    have heq : 800 + (i.val - 800) = i.val := by omega
    simpa only [heq] using h
  have h := refined_high_cells_09 ⟨i.val - 900, by omega⟩
  have heq : 900 + (i.val - 900) = i.val := by omega
  simpa only [heq] using h

#print axioms refined_high_cells

theorem refined_low_cells : ∀ i : Fin 1910, refinedLowCell i.val := by
  intro i
  by_cases h0 : i.val < 100
  · have h := refined_low_cells_00 ⟨i.val - 0, by omega⟩
    have heq : 0 + (i.val - 0) = i.val := by omega
    simpa only [heq] using h
  by_cases h1 : i.val < 200
  · have h := refined_low_cells_01 ⟨i.val - 100, by omega⟩
    have heq : 100 + (i.val - 100) = i.val := by omega
    simpa only [heq] using h
  by_cases h2 : i.val < 300
  · have h := refined_low_cells_02 ⟨i.val - 200, by omega⟩
    have heq : 200 + (i.val - 200) = i.val := by omega
    simpa only [heq] using h
  by_cases h3 : i.val < 400
  · have h := refined_low_cells_03 ⟨i.val - 300, by omega⟩
    have heq : 300 + (i.val - 300) = i.val := by omega
    simpa only [heq] using h
  by_cases h4 : i.val < 500
  · have h := refined_low_cells_04 ⟨i.val - 400, by omega⟩
    have heq : 400 + (i.val - 400) = i.val := by omega
    simpa only [heq] using h
  by_cases h5 : i.val < 600
  · have h := refined_low_cells_05 ⟨i.val - 500, by omega⟩
    have heq : 500 + (i.val - 500) = i.val := by omega
    simpa only [heq] using h
  by_cases h6 : i.val < 700
  · have h := refined_low_cells_06 ⟨i.val - 600, by omega⟩
    have heq : 600 + (i.val - 600) = i.val := by omega
    simpa only [heq] using h
  by_cases h7 : i.val < 800
  · have h := refined_low_cells_07 ⟨i.val - 700, by omega⟩
    have heq : 700 + (i.val - 700) = i.val := by omega
    simpa only [heq] using h
  by_cases h8 : i.val < 900
  · have h := refined_low_cells_08 ⟨i.val - 800, by omega⟩
    have heq : 800 + (i.val - 800) = i.val := by omega
    simpa only [heq] using h
  by_cases h9 : i.val < 1000
  · have h := refined_low_cells_09 ⟨i.val - 900, by omega⟩
    have heq : 900 + (i.val - 900) = i.val := by omega
    simpa only [heq] using h
  by_cases h10 : i.val < 1100
  · have h := refined_low_cells_10 ⟨i.val - 1000, by omega⟩
    have heq : 1000 + (i.val - 1000) = i.val := by omega
    simpa only [heq] using h
  by_cases h11 : i.val < 1200
  · have h := refined_low_cells_11 ⟨i.val - 1100, by omega⟩
    have heq : 1100 + (i.val - 1100) = i.val := by omega
    simpa only [heq] using h
  by_cases h12 : i.val < 1300
  · have h := refined_low_cells_12 ⟨i.val - 1200, by omega⟩
    have heq : 1200 + (i.val - 1200) = i.val := by omega
    simpa only [heq] using h
  by_cases h13 : i.val < 1400
  · have h := refined_low_cells_13 ⟨i.val - 1300, by omega⟩
    have heq : 1300 + (i.val - 1300) = i.val := by omega
    simpa only [heq] using h
  by_cases h14 : i.val < 1500
  · have h := refined_low_cells_14 ⟨i.val - 1400, by omega⟩
    have heq : 1400 + (i.val - 1400) = i.val := by omega
    simpa only [heq] using h
  by_cases h15 : i.val < 1600
  · have h := refined_low_cells_15 ⟨i.val - 1500, by omega⟩
    have heq : 1500 + (i.val - 1500) = i.val := by omega
    simpa only [heq] using h
  by_cases h16 : i.val < 1700
  · have h := refined_low_cells_16 ⟨i.val - 1600, by omega⟩
    have heq : 1600 + (i.val - 1600) = i.val := by omega
    simpa only [heq] using h
  by_cases h17 : i.val < 1800
  · have h := refined_low_cells_17 ⟨i.val - 1700, by omega⟩
    have heq : 1700 + (i.val - 1700) = i.val := by omega
    simpa only [heq] using h
  by_cases h18 : i.val < 1900
  · have h := refined_low_cells_18 ⟨i.val - 1800, by omega⟩
    have heq : 1800 + (i.val - 1800) = i.val := by omega
    simpa only [heq] using h
  have h := refined_low_cells_19 ⟨i.val - 1900, by omega⟩
  have heq : 1900 + (i.val - 1900) = i.val := by omega
  simpa only [heq] using h

#print axioms refined_low_cells

end Erdos883Verified
