import Erdos883SecondSixBlock
import Erdos883SecondSelectionMoments

/-! The six-block inequality applies to arbitrary fractional occupancies.
It is obtained by actual finite Bernoulli averaging, without rounding. -/

namespace Erdos883Second.Far

open scoped BigOperators
noncomputable section

def sixTriangleProducts (r : Fin 6 → ℝ) : ℝ :=
  r 0 * r 2 * r 4 + r 1 * r 0 * r 2 + r 1 * r 0 * r 4 +
  r 1 * r 2 * r 4 + r 3 * r 0 * r 2 + r 3 * r 0 * r 4 + r 3 * r 2 * r 4

theorem bitCount_cast (b : Bool) : (bitCount b : ℝ) = selectedBit b := by
  cases b <;> norm_num [bitCount, selectedBit]

theorem selectedBit_triple (a b c : Bool) :
    (bitCount (a && b && c) : ℝ) = selectedBit a * selectedBit b * selectedBit c := by
  cases a <;> cases b <;> cases c <;> norm_num [bitCount, selectedBit]

theorem six_bad_expectation (r : Fin 6 → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    (∑ s : Fin 6 → Bool, selectionWeight r s * (bitCount (sixBad s) : ℝ)) ≤
      sixTriangleProducts r := by
  have hp (s : Fin 6 → Bool) : (bitCount (sixBad s) : ℝ) ≤
      selectedBit (s 0) * selectedBit (s 2) * selectedBit (s 4) +
      selectedBit (s 1) * selectedBit (s 0) * selectedBit (s 2) +
      selectedBit (s 1) * selectedBit (s 0) * selectedBit (s 4) +
      selectedBit (s 1) * selectedBit (s 2) * selectedBit (s 4) +
      selectedBit (s 3) * selectedBit (s 0) * selectedBit (s 2) +
      selectedBit (s 3) * selectedBit (s 0) * selectedBit (s 4) +
      selectedBit (s 3) * selectedBit (s 2) * selectedBit (s 4) := by
    have h : (bitCount (sixBad s) : ℝ) ≤
        ((bitCount (s 0 && s 2 && s 4) +
        bitCount (s 1 && s 0 && s 2) + bitCount (s 1 && s 0 && s 4) +
        bitCount (s 1 && s 2 && s 4) +
        bitCount (s 3 && s 0 && s 2) + bitCount (s 3 && s 0 && s 4) +
        bitCount (s 3 && s 2 && s 4) : ℤ) : ℝ) := by
      exact_mod_cast six_bad_union_bound s
    simpa only [Int.cast_add, selectedBit_triple] using h
  have hs := Finset.sum_le_sum (fun s (_hs : s ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp s) (selectionWeight_nonneg r hr0 hr1 s))
  have h024 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 0) * selectedBit (s 2) * selectedBit (s 4))) = r 0 * r 2 * r 4 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({0,2,4} : Finset (Fin 6))
  have h102 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 1) * selectedBit (s 0) * selectedBit (s 2))) = r 1 * r 0 * r 2 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({1,0,2} : Finset (Fin 6))
  have h104 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 1) * selectedBit (s 0) * selectedBit (s 4))) = r 1 * r 0 * r 4 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({1,0,4} : Finset (Fin 6))
  have h124 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 1) * selectedBit (s 2) * selectedBit (s 4))) = r 1 * r 2 * r 4 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({1,2,4} : Finset (Fin 6))
  have h302 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 3) * selectedBit (s 0) * selectedBit (s 2))) = r 3 * r 0 * r 2 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({3,0,2} : Finset (Fin 6))
  have h304 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 3) * selectedBit (s 0) * selectedBit (s 4))) = r 3 * r 0 * r 4 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({3,0,4} : Finset (Fin 6))
  have h324 : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (selectedBit (s 3) * selectedBit (s 2) * selectedBit (s 4))) = r 3 * r 2 * r 4 := by
    simpa [selectedMonomial, mul_assoc] using selection_moment r ({3,2,4} : Finset (Fin 6))
  simpa only [mul_add, Finset.sum_add_distrib, h024, h102, h104, h124,
    h302, h304, h324, sixTriangleProducts] using hs

theorem six_fractional_pointwise (r : Fin 6 → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    3 - (r 1 + r 3 + r 5) ≤
      3 * (4 - (r 0 + r 1 + r 2 + r 3 + r 4 + r 5)) +
        6 * sixTriangleProducts r := by
  have heven : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (sixEvenSelected s : ℝ)) = r 1 + r 3 + r 5 := by
    simp only [sixEvenSelected, Int.cast_add, bitCount_cast, mul_add,
      Finset.sum_add_distrib, selection_first_moment]
  have hselected : (∑ s : Fin 6 → Bool, selectionWeight r s *
      (sixSelected s : ℝ)) = r 0 + r 1 + r 2 + r 3 + r 4 + r 5 := by
    simp only [sixSelected, Int.cast_add, bitCount_cast, mul_add,
      Finset.sum_add_distrib, selection_first_moment]
  have h := six_block_even_deficit (selectionWeight r) id
    ((r 1 + r 3 + r 5) / 3) ((r 0 + r 2 + r 4) / 3)
    (sixTriangleProducts r)
    (selectionWeight_nonneg r hr0 hr1) (selectionWeight_sum r)
    (by simp only [id_eq]; rw [heven]; ring)
    (by simp only [id_eq]; rw [hselected]; ring)
    (six_bad_expectation r hr0 hr1)
  linarith

#print axioms six_bad_expectation
#print axioms six_fractional_pointwise

end
end Erdos883Second.Far
