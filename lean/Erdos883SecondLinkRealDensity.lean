import Erdos883SecondLinkTriangles
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Real-valued, uniform triangle-density interface for the far-U argument.
The threshold is chosen before the integer set. This module does not assume
any signature approximation or arithmetic stability theorem. -/

namespace Erdos883Second.Link

noncomputable def orderedCoprimeTriangleDensity (A : Finset ℕ) (n : ℕ) : ℝ :=
  (orderedTriangleCount A coprimeRelation : ℝ) / (n : ℝ)^3

theorem ordered_coprime_triangle_density_lt_reciprocal (A : Finset ℕ)
    (n k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : A.card ≤ n) (hn : denseThreshold k l ≤ n)
    (hno : ¬ ContainsTripartite A l) :
    orderedCoprimeTriangleDensity A n < 1 / (k : ℝ) := by
  have ht := ordered_coprime_triangles_small_of_no_tripartite A n k l hk hl hA hn hno
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp [hn0] at ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have htR : (k : ℝ) * orderedTriangleCount A coprimeRelation < (n : ℝ)^3 := by
    exact_mod_cast ht
  unfold orderedCoprimeTriangleDensity
  apply (div_lt_iff₀ (pow_pos hnR 3)).mpr
  have hh : (orderedTriangleCount A coprimeRelation : ℝ) < (n : ℝ)^3 / k :=
    (lt_div_iff₀ hkR).mpr (by simpa only [mul_comm] using htR)
  simpa [div_eq_mul_inv, mul_comm] using hh

/-- For every positive real density, one threshold works for every finite
integer set whose cardinality is at most the prefix parameter. -/
theorem ordered_coprime_triangle_density_eventually_small (l : ℕ)
    (hl : 1 ≤ l) {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, A.card ≤ n →
      ¬ ContainsTripartite A l → orderedCoprimeTriangleDensity A n < gamma := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / gamma)
  have hkR : (0 : ℝ) < k := (one_div_pos.mpr hgamma).trans hk
  have hkN : 1 ≤ k := by
    have : 0 < k := Nat.cast_pos.mp hkR
    omega
  have hrecip : 1 / (k : ℝ) < gamma := by
    apply (div_lt_iff₀ hkR).mpr
    have hg := (div_lt_iff₀ hgamma).mp hk
    nlinarith
  refine ⟨denseThreshold k l, ?_⟩
  intro n hn A hA hno
  exact (ordered_coprime_triangle_density_lt_reciprocal A n k l hkN hl hA hn hno).trans hrecip

#print axioms ordered_coprime_triangle_density_lt_reciprocal
#print axioms ordered_coprime_triangle_density_eventually_small

end Erdos883Second.Link
