import Erdos883SecondFarComplete
import Erdos883VerifiedCoverage

/-! Exact original-problem coverage, and an explicit arithmetic witness check.
The first-question theorem is the existing attributed finite completion;
the second-question theorem is the independently derived development here. -/

namespace Erdos883Verified

theorem erdos883_bothQuestions :
    Erdos883Target.FirstQuestion ∧ Erdos883Second.SecondQuestion :=
  ⟨erdos883_firstQuestion, Erdos883Second.secondQuestion⟩

theorem erdos883_secondQuestion_raw :
    ∀ l : ℕ, 1 ≤ l → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        n / 2 + n / 3 - n / 6 < A.card →
        ∃ (a : ℕ) (b c : Fin l → ℕ),
          a ∈ A ∧ (∀ i, b i ∈ A) ∧ (∀ i, c i ∈ A) ∧
          Function.Injective b ∧ Function.Injective c ∧
          (∀ i, a ≠ b i) ∧ (∀ i, a ≠ c i) ∧ (∀ i j, b i ≠ c j) ∧
          (∀ i, Nat.Coprime a (b i)) ∧ (∀ i, Nat.Coprime a (c i)) ∧
          (∀ i j, Nat.Coprime (b i) (c j)) := by
  intro l hl
  obtain ⟨N, hN⟩ := Erdos883Second.secondQuestion l hl
  refine ⟨N, ?_⟩
  intro n hn A hA hcard
  let W := Erdos883Second.witnessOfContains (hN n hn A hA hcard)
  exact ⟨W.apex, W.left, W.right, W.apex_mem, W.left_mem, W.right_mem,
    W.left_injective, W.right_injective, W.apex_left_ne, W.apex_right_ne,
    W.left_right_ne, W.apex_left_coprime, W.apex_right_coprime, W.left_right_coprime⟩

-- The original all-n odd-simple-cycle assertion, with graph alias expanded.
example :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)).oddCycleLengths :=
  erdos883_firstQuestion

example : Erdos883Second.SecondQuestion =
    (∀ l : ℕ, 1 ≤ l → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        n / 2 + n / 3 - n / 6 < A.card →
        ∃ f : Erdos883Second.tripartiteGraph l →g
          ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)),
          Function.Injective f) := rfl

set_option pp.explicit true in
#check @erdos883_bothQuestions
#print Erdos883Target.FirstQuestion
#print Erdos883Second.SecondQuestion
#print Erdos883Second.ContainsTripartite
#print Erdos883Second.tripartiteGraph
#print Erdos883Second.part
#print SimpleGraph.cycleLengths
#print SimpleGraph.oddCycleLengths
#print axioms erdos883_firstQuestion
#print axioms Erdos883Second.farBranch
#print axioms Erdos883Second.secondQuestion
#print axioms erdos883_secondQuestion_raw
#print axioms erdos883_bothQuestions

end Erdos883Verified
