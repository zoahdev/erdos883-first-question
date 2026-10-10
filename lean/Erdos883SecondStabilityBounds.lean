import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Pure scalar steps in the independent far-U argument. The spectral premise
and conditional-moment identities are explicit hypotheses; this file is not a
proof of arithmetic stability or the full second question. -/

namespace Erdos883Second.Stability

theorem spectral_polynomial_lower {mu eps : ℝ}
    (_heps : 0 ≤ eps) (heps_small : eps ≤ 1 / 12)
    (hmu : 1 / 3 - 2 * eps ≤ mu) :
    -eps ≤ mu * (3 * mu - 1) / 2 := by
  have hx : 0 ≤ mu - (1 / 3 - 2 * eps) := by linarith
  have hy : 0 ≤ 3 * (mu + (1 / 3 - 2 * eps)) - 1 := by linarith
  nlinarith [mul_nonneg hx hy, sq_nonneg eps]

theorem spectral_errors_small {mu eps B I R : ℝ}
    (heps : 0 ≤ eps) (heps_small : eps ≤ 1 / 12)
    (hmu : 1 / 3 - 2 * eps ≤ mu) (hI : 0 ≤ I) (hR : 0 ≤ R)
    (hgap : mu * (3 * mu - 1) / 2 + I / 2 + R / 4 ≤ B) :
    0 ≤ B + eps ∧ I ≤ 2 * (B + eps) ∧ R ≤ 4 * (B + eps) := by
  have hg := spectral_polynomial_lower heps heps_small hmu
  constructor
  · linarith
  constructor <;> linarith

theorem mean_upper_of_spectral {mu B I R : ℝ}
    (hI : 0 ≤ I) (hR : 0 ≤ R)
    (hgap : mu * (3 * mu - 1) / 2 + I / 2 + R / 4 ≤ B) :
    mu ≤ 1 / 3 + 2 * B := by
  nlinarith [sq_nonneg (mu - 1 / 3)]

theorem outside_mass_small {mu eps B I R J a0 a1 : ℝ}
    (heps : 0 ≤ eps) (heps_small : eps ≤ 1 / 12)
    (hmu : 1 / 3 - 2 * eps ≤ mu) (hI : 0 ≤ I) (hR : 0 ≤ R)
    (hgap : mu * (3 * mu - 1) / 2 + I / 2 + R / 4 ≤ B)
    (hsmall : B + eps ≤ 1 / 48)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha1_le : a1 ≤ 1)
    (hmean : mu = (2 / 3) * a0 + (1 / 3) * a1)
    (hJsum : J = I + R)
    (hJconditional : J = (2 / 3) * a0 * (1 - a0) +
      (1 / 3) * a1 * (1 - a1)) :
    a0 / 3 ≤ 8 * (B + eps) := by
  obtain ⟨hh, hIle, hRle⟩ := spectral_errors_small heps heps_small hmu hI hR hgap
  have hmu_upper := mean_upper_of_spectral hI hR hgap
  have ha0_upper : a0 ≤ 9 / 16 := by linarith
  have hterm0 : 0 ≤ a0 * (9 / 16 - a0) :=
    mul_nonneg ha0 (by linarith)
  have hterm1 : 0 ≤ a1 * (1 - a1) :=
    mul_nonneg ha1 (by linarith)
  have hJlower : (7 / 24) * a0 ≤ J := by
    nlinarith
  have hJupper : J ≤ 6 * (B + eps) := by linarith
  linarith

theorem quantitative_far_contradiction {delta u h eta outside : ℝ}
    (hdelta : 0 < delta) (hu : u < delta / 32)
    (hh : h < u) (heta : eta < delta / 4)
    (hout : outside ≤ 8 * h + eta) (hfar : delta ≤ outside) : False := by
  linarith

end Erdos883Second.Stability

#print axioms Erdos883Second.Stability.spectral_polynomial_lower
#print axioms Erdos883Second.Stability.spectral_errors_small
#print axioms Erdos883Second.Stability.mean_upper_of_spectral
#print axioms Erdos883Second.Stability.outside_mass_small
#print axioms Erdos883Second.Stability.quantitative_far_contradiction
