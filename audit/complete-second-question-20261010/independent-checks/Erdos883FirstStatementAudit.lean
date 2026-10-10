import Erdos883VerifiedCoverage
import Erdos883SecondQuestion

/-! Independent statement/axiom audit only. The first-question theorem is
the user's existing, attributed theorem; no existing proof source is changed.
This file does not assert the full second question. -/

example : Erdos883Target.FirstQuestion := Erdos883Verified.erdos883_firstQuestion

example : Erdos883Target.FirstQuestion =
    (∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths) := rfl

example : Erdos883Second.SecondQuestion =
    (∀ l : ℕ, 1 ≤ l → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        n / 2 + n / 3 - n / 6 < A.card → Erdos883Second.ContainsTripartite A l) := rfl

#check Erdos883Verified.erdos883_firstQuestion
#check Erdos883Target.firstQuestion_iff_halfLength
#print Erdos883Target.FirstQuestion
#print Erdos883Second.SecondQuestion
#print Erdos883Second.ContainsTripartite
#print axioms Erdos883Verified.erdos883_firstQuestion
#print axioms Erdos883Target.firstQuestion_iff_halfLength
