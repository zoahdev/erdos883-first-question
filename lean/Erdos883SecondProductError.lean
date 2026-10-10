import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite L1 error for replacing three independent signature measures.
The empirical integer-signature approximation must be supplied by the
separate CRT theorem. -/

namespace Erdos883Second.Far

open scoped BigOperators
noncomputable section

def tripleWeight {α : Type*} (w : α → ℝ) (x : α × α × α) : ℝ :=
  w x.1 * w x.2.1 * w x.2.2

theorem tripleWeight_sum {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : (∑ x, w x) = 1) :
    (∑ x : α × α × α, tripleWeight w x) = 1 := by
  simp [tripleWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    ← Finset.sum_mul, hw]

theorem tripleWeight_l1 {α : Type*} [Fintype α] (w v : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 ≤ v x)
    (hw_sum : (∑ x, w x) = 1) (hv_sum : (∑ x, v x) = 1) :
    (∑ x : α × α × α, |tripleWeight w x - tripleWeight v x|) ≤
      3 * ∑ x, |w x - v x| := by
  have hpoint (x : α × α × α) :
      |tripleWeight w x - tripleWeight v x| ≤
        |w x.1 - v x.1| * w x.2.1 * w x.2.2 +
        v x.1 * |w x.2.1 - v x.2.1| * w x.2.2 +
        v x.1 * v x.2.1 * |w x.2.2 - v x.2.2| := by
    have he : tripleWeight w x - tripleWeight v x =
        (w x.1 - v x.1) * w x.2.1 * w x.2.2 +
        v x.1 * (w x.2.1 - v x.2.1) * w x.2.2 +
        v x.1 * v x.2.1 * (w x.2.2 - v x.2.2) := by
      unfold tripleWeight
      ring
    rw [he]
    calc
      _ ≤ |(w x.1 - v x.1) * w x.2.1 * w x.2.2 +
          v x.1 * (w x.2.1 - v x.2.1) * w x.2.2| +
          |v x.1 * v x.2.1 * (w x.2.2 - v x.2.2)| := abs_add_le _ _
      _ ≤ (|(w x.1 - v x.1) * w x.2.1 * w x.2.2| +
          |v x.1 * (w x.2.1 - v x.2.1) * w x.2.2|) +
          |v x.1 * v x.2.1 * (w x.2.2 - v x.2.2)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by simp only [abs_mul, abs_of_nonneg (hw _), abs_of_nonneg (hv _)]
  have hs := Finset.sum_le_sum (fun x (_hx : x ∈ Finset.univ) => hpoint x)
  have hfactor : (∑ x : α × α × α,
        (|w x.1 - v x.1| * w x.2.1 * w x.2.2 +
        v x.1 * |w x.2.1 - v x.2.1| * w x.2.2 +
        v x.1 * v x.2.1 * |w x.2.2 - v x.2.2|)) =
      3 * ∑ x, |w x - v x| := by
    simp only [Finset.sum_add_distrib, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hw_sum, hv_sum,
      mul_one, one_mul]
    ring
  exact hfactor ▸ hs

theorem triple_expectation_error {α : Type*} [Fintype α]
    (w v : α → ℝ) (f : α × α × α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 ≤ v x)
    (hw_sum : (∑ x, w x) = 1) (hv_sum : (∑ x, v x) = 1)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(∑ x, tripleWeight w x * f x) - (∑ x, tripleWeight v x * f x)| ≤
      3 * ∑ x, |w x - v x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |tripleWeight w x * f x - tripleWeight v x * f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |tripleWeight w x - tripleWeight v x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, abs_mul, abs_of_nonneg (hf0 x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf1 x)
    _ ≤ _ := tripleWeight_l1 w v hw hv hw_sum hv_sum

end

#print axioms tripleWeight_sum
#print axioms tripleWeight_l1
#print axioms triple_expectation_error

end Erdos883Second.Far
