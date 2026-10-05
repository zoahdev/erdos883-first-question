import Erdos883FiniteCriterion

namespace Erdos883Verified

/-- Concrete rank witness used by the manuscript's smallest-feasible-prefix checker. -/
def intervalWitness (L U : ℕ) (O ps : List ℕ) (b j s : ℕ) : Prop :=
  let p := halfOdds U - b - (j - signatureBudget s - 1) / 2
  p ≤ halfOdds U ∧ 2 * (halfOdds U - p - b) + signatureBudget s < j ∧
    ((∀ u ∈ orderPrefix O p, ∀ v ∈ orderPrefix O p, u ≠ v →
        divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
        b + j ≤ (rawCommon Nat.Coprime (evenUniverse L) u v).card) ∨
     (∀ u ∈ orderPrefix O p, ∀ v ∈ orderPrefix O p, u ≠ v →
        divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
        U - threshold U + maxHalfLength U + j ≤
          (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card))

/-- A finite, decidable check, whose successful result is proved sound below. -/
def finiteIntervalCheck (L U : ℕ) (O ps : List ℕ) : Prop :=
  ∀ b : Fin (halfOdds U - retainedOdds U + 1),
    ∀ j : Fin (maxHalfLength U),
      ∃ s : Fin (ps.length + 1), intervalWitness L U O ps b.val (j.val + 1) s.val

theorem exactCertificate_of_finiteCheck {L U : ℕ} {O ps : List ℕ}
    (hcheck : finiteIntervalCheck L U O ps) : ExactIntervalCertificate L U O ps := by
  intro b hb j hj hjU
  obtain ⟨s, hs⟩ := hcheck ⟨b, by omega⟩ ⟨j - 1, by omega⟩
  have hjEq : j - 1 + 1 = j := by omega
  simp only [hjEq] at hs
  exact ⟨s.val, by omega,
    halfOdds U - b - (j - signatureBudget s.val - 1) / 2, hs⟩

#print axioms exactCertificate_of_finiteCheck
end Erdos883Verified
