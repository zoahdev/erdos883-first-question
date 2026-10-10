import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact 64-case inequality behind the six-block stability argument.
Offsets 1,...,6 are indexed by 0,...,5. This does not assume that these
offsets themselves are pairwise coprime: the arithmetic signature coupling
is a separate construction. -/

namespace Erdos883Second.Far

open scoped BigOperators

def bitCount (b : Bool) : ℤ := if b then 1 else 0

def sixSelected (s : Fin 6 → Bool) : ℤ :=
  bitCount (s 0) + bitCount (s 1) + bitCount (s 2) +
  bitCount (s 3) + bitCount (s 4) + bitCount (s 5)

def sixEvenSelected (s : Fin 6 → Bool) : ℤ :=
  bitCount (s 1) + bitCount (s 3) + bitCount (s 5)

def sixBad (s : Fin 6 → Bool) : Bool :=
  (s 0 && s 2 && s 4) ||
  (s 1 && s 0 && s 2) || (s 1 && s 0 && s 4) ||
  (s 1 && s 2 && s 4) ||
  (s 3 && s 0 && s 2) || (s 3 && s 0 && s 4) ||
  (s 3 && s 2 && s 4)

theorem six_block_pointwise (s : Fin 6 → Bool) :
    3 - sixEvenSelected s ≤ 3 * (4 - sixSelected s) + 6 * bitCount (sixBad s) := by
  unfold sixEvenSelected sixSelected sixBad bitCount
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    cases h3 : s 3 <;> cases h4 : s 4 <;> cases h5 : s 5 <;> decide

theorem six_bad_union_bound (s : Fin 6 → Bool) :
    bitCount (sixBad s) ≤
      bitCount (s 0 && s 2 && s 4) +
      bitCount (s 1 && s 0 && s 2) + bitCount (s 1 && s 0 && s 4) +
      bitCount (s 1 && s 2 && s 4) +
      bitCount (s 3 && s 0 && s 2) + bitCount (s 3 && s 0 && s 4) +
      bitCount (s 3 && s 2 && s 4) := by
  unfold sixBad bitCount
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    cases h3 : s 3 <;> cases h4 : s 4 <;> cases h5 : s 5 <;> decide

theorem six_block_even_deficit {α : Type*} [Fintype α]
    (w : α → ℝ) (s : α → Fin 6 → Bool) (E O r : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_sum : (∑ x, w x) = 1)
    (h_even : (∑ x, w x * (sixEvenSelected (s x) : ℝ)) = 3 * E)
    (h_selected : (∑ x, w x * (sixSelected (s x) : ℝ)) = 3 * E + 3 * O)
    (h_bad : (∑ x, w x * (bitCount (sixBad (s x)) : ℝ)) ≤ r) :
    1 - E ≤ 4 - 3 * E - 3 * O + 2 * r := by
  have hpoint : (∑ x, w x * (3 - (sixEvenSelected (s x) : ℝ))) ≤
      ∑ x, w x * (3 * (4 - (sixSelected (s x) : ℝ)) +
        6 * (bitCount (sixBad (s x)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hw x)
    exact_mod_cast six_block_pointwise (s x)
  have hleft : (∑ x, w x * (3 - (sixEvenSelected (s x) : ℝ))) = 3 - 3 * E := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hw_sum, h_even]
    ring
  have hright : (∑ x, w x * (3 * (4 - (sixSelected (s x) : ℝ)) +
        6 * (bitCount (sixBad (s x)) : ℝ))) =
      12 - 3 * (3 * E + 3 * O) +
        6 * (∑ x, w x * (bitCount (sixBad (s x)) : ℝ)) := by
    simp_rw [mul_add, mul_sub]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [show ∀ x, w x * (3 * 4) = w x * 12 by intro x; ring,
      show ∀ x, w x * (3 * (sixSelected (s x) : ℝ)) =
        3 * (w x * (sixSelected (s x) : ℝ)) by intro x; ring,
      show ∀ x, w x * (6 * (bitCount (sixBad (s x)) : ℝ)) =
        6 * (w x * (bitCount (sixBad (s x)) : ℝ)) by intro x; ring]
    rw [← Finset.sum_mul, hw_sum, ← Finset.mul_sum, h_selected,
      ← Finset.mul_sum]
    ring
  rw [hleft, hright] at hpoint
  linarith

#print axioms six_block_pointwise
#print axioms six_bad_union_bound
#print axioms six_block_even_deficit

end Erdos883Second.Far
