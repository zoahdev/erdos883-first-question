import Erdos883ImprovedLargeNCover

namespace Erdos883Verified

/-- The exact canonical conclusion restricted to one closed interval of n. -/
def FirstQuestionOn (L U : ℕ) : Prop :=
  ∀ (n : ℕ), L ≤ n → n ≤ U → ∀ (A : Finset ℕ),
    A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
    ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
      l ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

/-- Adjacent interval proofs compose without any numerical search or coverage assumption. -/
theorem firstQuestionOn_join {L M U : ℕ}
    (hleft : FirstQuestionOn L M) (hright : FirstQuestionOn (M+1) U) :
    FirstQuestionOn L U := by
  intro n hnL hnU A hA hd l hl h3 hln
  by_cases hnM : n ≤ M
  · exact hleft n hnL hnM A hA hd l hl h3 hln
  · exact hright n (by omega) hnU A hA hd l hl h3 hln

theorem firstQuestionOn_restrict {L U L' U' : ℕ}
    (h : FirstQuestionOn L U) (hL : L ≤ L') (hU : U' ≤ U) :
    FirstQuestionOn L' U' := by
  intro n hnL hnU A hA hd l hl h3 hln
  exact h n (hL.trans hnL) (hnU.trans hU) A hA hd l hl h3 hln

/-- Conversion from the verified interval certificates' half-length formulation. -/
theorem firstQuestionOn_of_halfLength {L U : ℕ}
    (h : ∀ n : ℕ, L ≤ n → n ≤ U → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → threshold n < A.card →
      ∀ k : ℕ, 1 ≤ k → k ≤ maxHalfLength n →
        2*k+1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths) :
    FirstQuestionOn L U := by
  intro n hnL hnU A hA hd l hl h3 hln
  obtain ⟨k,hk,hkn,rfl⟩ := (length_range_iff n l).mp ⟨hl,h3,hln⟩
  exact h n hnL hnU A hA hd k hk hkn

/-- Final assembly interface. The finite interval proof is still required. -/
theorem firstQuestion_of_initial_interval
    (hfinite : FirstQuestionOn 0 199999) : Erdos883Target.FirstQuestion := by
  intro n A hA hd l hl h3 hln
  by_cases hn : n ≤ 199999
  · exact hfinite n (Nat.zero_le _) hn A hA hd l hl h3 hln
  · exact Improved.firstQuestion_largeN n (by omega) A hA hd l hl h3 hln

#print axioms firstQuestionOn_join
#print axioms firstQuestionOn_restrict
#print axioms firstQuestionOn_of_halfLength
#print axioms firstQuestion_of_initial_interval
end Erdos883Verified
