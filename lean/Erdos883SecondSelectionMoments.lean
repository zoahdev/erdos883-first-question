import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Exact moments for independent finite Bernoulli selections. -/

namespace Erdos883Second.Far

open scoped BigOperators
noncomputable section

def selectionCoordinate (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r
def selectedBit (b : Bool) : ℝ := if b then 1 else 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def selectionWeight (r : ι → ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, selectionCoordinate (r i) (s i)

def selectedMonomial (s : ι → Bool) (J : Finset ι) : ℝ :=
  ∏ i ∈ J, selectedBit (s i)

theorem selectionWeight_nonneg (r : ι → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) (s : ι → Bool) :
    0 ≤ selectionWeight r s := by
  apply Finset.prod_nonneg
  intro i _
  cases s i <;> simp [selectionCoordinate, hr0, sub_nonneg.mpr (hr1 i)]

theorem selectionWeight_sum (r : ι → ℝ) :
    (∑ s : ι → Bool, selectionWeight r s) = 1 := by
  unfold selectionWeight
  rw [← Fintype.prod_sum]
  simp [selectionCoordinate]

theorem selection_moment (r : ι → ℝ) (J : Finset ι) :
    (∑ s : ι → Bool, selectionWeight r s * selectedMonomial s J) =
      ∏ i ∈ J, r i := by
  have hpoint (s : ι → Bool) : selectionWeight r s * selectedMonomial s J =
      ∏ i, (selectionCoordinate (r i) (s i) *
        if i ∈ J then selectedBit (s i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [selectionWeight, selectedMonomial, Finset.prod_ite_mem]
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun i b => selectionCoordinate (r i) b *
    (if i ∈ J then selectedBit b else 1))]
  have hcoordinate (i : ι) : (∑ b : Bool, selectionCoordinate (r i) b *
      if i ∈ J then selectedBit b else 1) = if i ∈ J then r i else 1 := by
    by_cases hi : i ∈ J <;> simp [hi, selectionCoordinate, selectedBit]
  simp_rw [hcoordinate]
  simp [Finset.prod_ite_mem]

theorem selection_first_moment (r : ι → ℝ) (i : ι) :
    (∑ s : ι → Bool, selectionWeight r s * selectedBit (s i)) = r i := by
  simpa [selectedMonomial] using selection_moment r {i}

#print axioms selectionWeight_sum
#print axioms selection_moment
#print axioms selection_first_moment

end
end Erdos883Second.Far
