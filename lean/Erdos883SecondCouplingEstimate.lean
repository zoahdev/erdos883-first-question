import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite Cauchy--Schwarz step for a supported coupling. The arithmetic
coupling and its marginals still have to be constructed separately. -/

namespace Erdos883Second.Far

open scoped BigOperators
noncomputable section

theorem coupling_expectation_sq_bound {α : Type*} [Fintype α]
    (w m f : α → ℝ) (allowed : α → Prop) [DecidablePred allowed]
    (hw : ∀ x, 0 < w x) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, ¬ allowed x → m x = 0) :
    (∑ x, m x * f x)^2 ≤ (∑ x, (m x)^2 / w x) *
      ∑ x, if allowed x then w x * f x else 0 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro x _
    exact div_nonneg (sq_nonneg _) (le_of_lt (hw x))
  · intro x _
    split_ifs
    · exact mul_nonneg (le_of_lt (hw x)) (hf0 x)
    · exact le_rfl
  · intro x _
    by_cases hx : allowed x
    · simp only [if_pos hx]
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (hw x))]
      have hfsq : (f x)^2 ≤ f x := by
        nlinarith [mul_nonneg (hf0 x) (sub_nonneg.mpr (hf1 x))]
      nlinarith [mul_le_mul_of_nonneg_left hfsq (sq_nonneg (m x))]
    · simp [hx, hsupport x hx]

theorem coupling_expectation_bound {α : Type*} [Fintype α]
    (w m f : α → ℝ) (allowed : α → Prop) [DecidablePred allowed]
    (C D : ℝ) (hw : ∀ x, 0 < w x)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, ¬ allowed x → m x = 0)
    (hC : 0 ≤ C) (hL2 : (∑ x, (m x)^2 / w x) ≤ C^2)
    (hD : (∑ x, if allowed x then w x * f x else 0) ≤ D) :
    (∑ x, m x * f x) ≤ C * Real.sqrt D := by
  have hmass : 0 ≤ ∑ x, if allowed x then w x * f x else 0 := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact mul_nonneg (le_of_lt (hw x)) (hf0 x)
    · exact le_rfl
  have hD0 : 0 ≤ D := hmass.trans hD
  have hs := coupling_expectation_sq_bound w m f allowed hw hf0 hf1 hsupport
  have hs' : (∑ x, m x * f x)^2 ≤ C^2 * D :=
    hs.trans (mul_le_mul hL2 hD hmass (sq_nonneg C))
  have hsqrt := Real.sq_sqrt hD0
  have hroot : 0 ≤ C * Real.sqrt D := mul_nonneg hC (Real.sqrt_nonneg D)
  nlinarith [sq_nonneg ((∑ x, m x * f x) - C * Real.sqrt D)]

end

#print axioms coupling_expectation_sq_bound
#print axioms coupling_expectation_bound

end Erdos883Second.Far
