import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Eventual finite counting budgets with all parameters chosen before n. -/

namespace Erdos883Second.Far

theorem counting_budgets_eventually (M : ℕ) (s g delta : ℝ)
    (hs : 0 < s) (hg : 0 < g) (hd : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n ∧
      (2 + (M : ℝ)) / n ≤ s / 14 ∧
      3 * (M : ℝ) / n ≤ g / 2 ∧ (M : ℝ) / n ≤ delta / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (14 * (2 + (M : ℝ)) / s + 6 * (M : ℝ) / g + 4 * (M : ℝ) / delta + 1)
  refine ⟨N, ?_⟩
  intro n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 ≤ 14 * (2 + (M : ℝ)) / s := by positivity
  have h2 : 0 ≤ 6 * (M : ℝ) / g := by positivity
  have h3 : 0 ≤ 4 * (M : ℝ) / delta := by positivity
  have hnR : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hn1 : 14 * (2 + (M : ℝ)) / s ≤ n := by linarith
  have hn2 : 6 * (M : ℝ) / g ≤ n := by linarith
  have hn3 : 4 * (M : ℝ) / delta ≤ n := by linarith
  have hb1 := (div_le_iff₀ hs).mp hn1
  have hb2 := (div_le_iff₀ hg).mp hn2
  have hb3 := (div_le_iff₀ hd).mp hn3
  refine ⟨hn0, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hnR).mpr
    nlinarith
  · apply (div_le_iff₀ hnR).mpr
    nlinarith
  · apply (div_le_iff₀ hnR).mpr
    nlinarith

theorem signature_error_budget {s eps D : ℝ} (hs : 0 < s)
    (heps : eps ≤ s / 14) (hD : D ≤ (s / 2784)^2) :
    7 * eps + 1392 * Real.sqrt D ≤ s := by
  have hsqrt : Real.sqrt D ≤ s / 2784 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hD⟩
  linarith

#print axioms counting_budgets_eventually
#print axioms signature_error_budget

end Erdos883Second.Far
