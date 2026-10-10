import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Elementary spectral data for the independently derived far-U argument.

The coordinate kernel is the disjoint-pair kernel on a Bernoulli(1/p)
coordinate. This file does not assert the full second-question theorem or
assume any arithmetic stability result. It contains no previous
second-question proof code.
-/

namespace Erdos883.SecondSpectral

noncomputable section

/-- Coordinate Markov operator, with `true` meaning divisibility by the prime. -/
def coordinateKernel (p : ℝ) (f : Bool → ℝ) : Bool → ℝ
  | false => ((p - 2) / (p - 1)) * f false + (1 / (p - 1)) * f true
  | true => f false

/-- Expectation for the Bernoulli(1/p) stationary measure. -/
def coordinateMean (p : ℝ) (f : Bool → ℝ) : ℝ :=
  ((p - 1) / p) * f false + (1 / p) * f true

/-- The unnormalized centered coordinate; no square roots are needed. -/
def centeredCoordinate (p : ℝ) : Bool → ℝ
  | false => -(1 / p)
  | true => 1 - 1 / p

def coordinateEigenvalue (p : ℝ) : ℝ := -(1 / (p - 1))

def coordinateInner (p : ℝ) (f g : Bool → ℝ) : ℝ :=
  ((p - 1) / p) * f false * g false + (1 / p) * f true * g true

theorem coordinateKernel_add (p : ℝ) (f g : Bool → ℝ) :
    coordinateKernel p (fun b => f b + g b) =
      fun b => coordinateKernel p f b + coordinateKernel p g b := by
  funext b
  cases b with
  | false => dsimp [coordinateKernel]; ring
  | true => rfl

theorem coordinateKernel_smul (p c : ℝ) (f : Bool → ℝ) :
    coordinateKernel p (fun b => c * f b) =
      fun b => c * coordinateKernel p f b := by
  funext b
  cases b with
  | false => dsimp [coordinateKernel]; ring
  | true => rfl

theorem coordinateKernel_const (p c : ℝ) (hp : p ≠ 1) :
    coordinateKernel p (fun _ => c) = fun _ => c := by
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  funext b
  cases b <;> simp [coordinateKernel]
  field_simp
  ring

theorem centeredCoordinate_mean_zero (p : ℝ) (hp : p ≠ 0) :
    coordinateMean p (centeredCoordinate p) = 0 := by
  simp [coordinateMean, centeredCoordinate]
  field_simp
  ring

theorem coordinateKernel_centered (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    coordinateKernel p (centeredCoordinate p) =
      fun b => coordinateEigenvalue p * centeredCoordinate p b := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  funext b
  cases b <;> simp [coordinateKernel, centeredCoordinate, coordinateEigenvalue]
  all_goals field_simp
  all_goals ring

theorem coordinateKernel_stationary (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (f : Bool → ℝ) :
    coordinateMean p (coordinateKernel p f) = coordinateMean p f := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  simp [coordinateMean, coordinateKernel]
  field_simp
  ring

theorem coordinateKernel_reversible (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (f g : Bool → ℝ) :
    coordinateInner p f (coordinateKernel p g) =
      coordinateInner p (coordinateKernel p f) g := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  simp [coordinateInner, coordinateKernel]
  field_simp
  ring

theorem coordinateVariance_identity (p : ℝ) (hp : p ≠ 0) (f : Bool → ℝ) :
    coordinateInner p f f - (coordinateMean p f)^2 =
      ((p - 1) / p^2) * (f true - f false)^2 := by
  simp [coordinateInner, coordinateMean]
  field_simp
  ring

theorem coordinatePair_identity (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (f : Bool → ℝ) :
    coordinateInner p f (coordinateKernel p f) =
      (coordinateMean p f)^2 + coordinateEigenvalue p *
        (coordinateInner p f f - (coordinateMean p f)^2) := by
  have hp : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  simp [coordinateInner, coordinateMean, coordinateKernel, coordinateEigenvalue]
  field_simp
  ring

theorem coordinateEigenvalue_three : coordinateEigenvalue 3 = -(1 / 2 : ℝ) := by
  norm_num [coordinateEigenvalue]

theorem coordinateEigenvalue_nonpos (p : ℝ) (hp : 3 ≤ p) :
    coordinateEigenvalue p ≤ 0 := by
  have h : 0 ≤ 1 / (p - 1) :=
    div_nonneg (by norm_num) (by linarith)
  simpa [coordinateEigenvalue] using neg_nonpos.mpr h

theorem coordinateEigenvalue_ge_half (p : ℝ) (hp : 3 ≤ p) :
    -(1 / 2 : ℝ) ≤ coordinateEigenvalue p := by
  have h : (1 : ℝ) / (p - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  simpa [coordinateEigenvalue] using neg_le_neg h

theorem coordinateEigenvalue_ge_quarter (p : ℝ) (hp : 5 ≤ p) :
    -(1 / 4 : ℝ) ≤ coordinateEigenvalue p := by
  have h : (1 : ℝ) / (p - 1) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  simpa [coordinateEigenvalue] using neg_le_neg h

end

end Erdos883.SecondSpectral

#print axioms Erdos883.SecondSpectral.coordinateKernel_centered
#print axioms Erdos883.SecondSpectral.coordinateKernel_reversible
#print axioms Erdos883.SecondSpectral.coordinatePair_identity
#print axioms Erdos883.SecondSpectral.coordinateEigenvalue_ge_quarter
