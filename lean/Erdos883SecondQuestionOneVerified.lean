import Erdos883SecondQuestionOne
import Erdos883VerifiedCoverage

namespace Erdos883Second

/-- Verified `l=1` subcase using the user's existing first-question theorem.
The existing first-question dependency retains its original attribution. -/
theorem secondQuestion_one_verified :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
        ContainsTripartite A 1 :=
  firstQuestion_implies_secondQuestion_one Erdos883Verified.erdos883_firstQuestion

#print axioms secondQuestion_one_verified

end Erdos883Second
