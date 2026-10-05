import Erdos883VerifiedCoverage

/-
Automated verification harness for the final all-n theorem.
This file must only be compiled after the final theorem has been assembled.
-/

set_option pp.explicit true in
#check @Erdos883Verified.erdos883_firstQuestion

-- The original canonical right-hand side, with the coprime graph alias expanded.
example :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)).oddCycleLengths :=
  Erdos883Verified.erdos883_firstQuestion

-- Independently verify that the named project goal expands to that same proposition.
example : Erdos883Target.FirstQuestion =
    (∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)).oddCycleLengths) := rfl

#print Erdos883Target.FirstQuestion
#print Erdos883Target.coprimeGraph
#print SimpleGraph.cycleLengths
#print SimpleGraph.oddCycleLengths
#print axioms Erdos883Verified.erdos883_firstQuestion
