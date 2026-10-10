import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-! Pushforward of a finite product law factors coordinate by coordinate. -/

namespace Erdos883Second.Far

open scoped BigOperators
noncomputable section

def fiberMass {β γ : Type*} [Fintype β] [DecidableEq γ]
    (w : β → ℝ) (φ : β → γ) (y : γ) : ℝ :=
  ∑ x, if φ x = y then w x else 0

def productMass {ι β : Type*} [Fintype ι] (w : ι → β → ℝ) (x : ι → β) : ℝ :=
  ∏ i, w i (x i)

def productMap {ι β γ : Type*} (φ : ι → β → γ) (x : ι → β) : ι → γ :=
  fun i => φ i (x i)

theorem expectation_pushforward {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq γ] (w : β → ℝ) (φ : β → γ) (f : γ → ℝ) :
    (∑ x, w x * f (φ x)) = ∑ y, fiberMass w φ y * f y := by
  classical
  simp only [fiberMass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem product_fiberMass {ι β γ : Type*} [Fintype ι] [Fintype β]
    [DecidableEq ι] [DecidableEq γ]
    (w : ι → β → ℝ) (φ : ι → β → γ) (y : ι → γ) :
    fiberMass (productMass w) (productMap φ) y =
      productMass (fun i => fiberMass (w i) (φ i)) y := by
  classical
  unfold fiberMass productMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ht : productMap φ x = y
  · simp only [if_pos ht]
    have he (i : ι) : φ i (x i) = y i := congrFun ht i
    simp only [he, if_true]
  · simp only [if_neg ht]
    have hex : ∃ i, φ i (x i) ≠ y i := by
      by_contra hn
      push_neg at hn
      exact ht (funext hn)
    obtain ⟨i, hi⟩ := hex
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem product_expectation_pushforward {ι β γ : Type*} [Fintype ι]
    [Fintype β] [Fintype γ] [DecidableEq ι] [DecidableEq γ]
    (w : ι → β → ℝ) (φ : ι → β → γ) (f : (ι → γ) → ℝ) :
    (∑ x : ι → β, productMass w x * f (productMap φ x)) =
      ∑ y : ι → γ, productMass (fun i => fiberMass (w i) (φ i)) y * f y := by
  rw [expectation_pushforward]
  simp_rw [product_fiberMass]

theorem productMass_sum {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq ι] (w : ι → β → ℝ) (hw : ∀ i, (∑ b, w i b) = 1) :
    (∑ x : ι → β, productMass w x) = 1 := by
  unfold productMass
  rw [← Fintype.prod_sum]
  simp [hw]

#print axioms expectation_pushforward
#print axioms product_fiberMass
#print axioms product_expectation_pushforward
#print axioms productMass_sum

end
end Erdos883Second.Far
