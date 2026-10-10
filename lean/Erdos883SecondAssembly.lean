import Erdos883SecondNearComplete

/-! The final quantifier assembly. Its far-branch premise is explicit and
must be proved before this can certify the second question. -/

namespace Erdos883Second

def FarBranch : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ δ : ℚ, 0 < δ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
      δ * n ≤ ((A \ Near.standardUniverse n).card : ℚ) → ContainsTripartite A l

theorem secondQuestion_of_farBranch (hfar : FarBranch) : SecondQuestion := by
  intro l hl
  obtain ⟨δ, hδ, Nnear, hnear⟩ := Near.near_tripartite_eventually l
  obtain ⟨Nfar, hfarN⟩ := hfar l hl δ hδ
  refine ⟨max Nnear Nfar, ?_⟩
  intro n hn A hA hcard
  by_cases ht : ((A \ Near.standardUniverse n).card : ℚ) ≤ δ * n
  · exact hnear n ((Nat.le_max_left _ _).trans hn) A hA hcard ht
  · exact hfarN n ((Nat.le_max_right _ _).trans hn) A hA hcard (le_of_not_ge ht)

#print axioms secondQuestion_of_farBranch

end Erdos883Second
