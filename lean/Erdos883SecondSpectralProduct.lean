import Erdos883SecondSpectralKernel
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-!
Finite product eigenvalue bounds for the odd-prime disjoint-pair chain.

The future tensor-basis construction can use `tensorEigenvalue_ge_quarter`
directly: the singleton coordinate `{3}` has eigenvalue `-1/2`, whereas
every other odd-prime support has eigenvalue at least `-1/4`.
-/

namespace Erdos883.SecondSpectral

noncomputable section

def tensorEigenvalue (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, coordinateEigenvalue (p : ℝ)

theorem coordinateEigenvalue_abs_le_half (p : ℝ) (hp : 3 ≤ p) :
    |coordinateEigenvalue p| ≤ (1 / 2 : ℝ) := by
  apply abs_le.mpr
  exact ⟨coordinateEigenvalue_ge_half p hp,
    (coordinateEigenvalue_nonpos p hp).trans (by norm_num)⟩

theorem tensorEigenvalue_abs_le_pow (S : Finset ℕ)
    (hS : ∀ p ∈ S, 3 ≤ p) :
    |tensorEigenvalue S| ≤ (1 / 2 : ℝ)^S.card := by
  rw [tensorEigenvalue, Finset.abs_prod]
  calc
    (∏ p ∈ S, |coordinateEigenvalue (p : ℝ)|)
        ≤ ∏ p ∈ S, (1 / 2 : ℝ) := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro p hp
          apply coordinateEigenvalue_abs_le_half
          exact_mod_cast hS p hp
    _ = (1 / 2 : ℝ)^S.card := by simp

theorem tensorEigenvalue_abs_le_half (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, 3 ≤ p) :
    |tensorEigenvalue S| ≤ (1 / 2 : ℝ) := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hne
  calc
    |tensorEigenvalue S| ≤ (1 / 2 : ℝ)^S.card := tensorEigenvalue_abs_le_pow S hS
    _ ≤ (1 / 2 : ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    _ = (1 / 2 : ℝ) := by simp

theorem tensorEigenvalue_abs_le_quarter (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (hS : ∀ p ∈ S, 3 ≤ p) :
    |tensorEigenvalue S| ≤ (1 / 4 : ℝ) := by
  calc
    |tensorEigenvalue S| ≤ (1 / 2 : ℝ)^S.card := tensorEigenvalue_abs_le_pow S hS
    _ ≤ (1 / 2 : ℝ)^2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    _ = (1 / 4 : ℝ) := by norm_num

theorem tensorEigenvalue_singleton_three :
    tensorEigenvalue {3} = -(1 / 2 : ℝ) := by
  simp [tensorEigenvalue, coordinateEigenvalue_three]

theorem tensorEigenvalue_ge_half (S : Finset ℕ)
    (hS : ∀ p ∈ S, 3 ≤ p) :
    -(1 / 2 : ℝ) ≤ tensorEigenvalue S := by
  by_cases hne : S.Nonempty
  · exact (abs_le.mp (tensorEigenvalue_abs_le_half S hne hS)).1
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he, tensorEigenvalue]
    norm_num

theorem tensorEigenvalue_ge_quarter (S : Finset ℕ) (hne : S ≠ {3})
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    -(1 / 4 : ℝ) ≤ tensorEigenvalue S := by
  by_cases hc0 : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp hc0
    simp [he, tensorEigenvalue]
    norm_num
  by_cases hc1 : S.card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc1
    have hpS : p ∈ S := by simp [hp]
    have hpp := (hS p hpS).1
    have hp3 := (hS p hpS).2
    have hpn3 : p ≠ 3 := by
      intro he
      subst p
      exact hne hp
    have hp5 : 5 ≤ p := hpp.five_le_of_ne_two_of_ne_three (by omega) hpn3
    simpa [hp, tensorEigenvalue] using
      coordinateEigenvalue_ge_quarter (p : ℝ) (by exact_mod_cast hp5)
  · have hc2 : 2 ≤ S.card := by omega
    exact (abs_le.mp (tensorEigenvalue_abs_le_quarter S hc2
      (fun p hp => (hS p hp).2))).1

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.tensorEigenvalue_abs_le_pow
#print axioms Erdos883.SecondSpectral.tensorEigenvalue_ge_half
#print axioms Erdos883.SecondSpectral.tensorEigenvalue_ge_quarter
