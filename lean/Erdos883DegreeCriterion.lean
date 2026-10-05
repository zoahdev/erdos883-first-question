import Erdos883ProfileCriterion

namespace Erdos883Verified

/-- Number of odd vertices whose integer degree lower bound is strictly below
`K`. Vertices equal to the threshold remain available. -/
def lowDegreeCount (degree : ℕ → ℕ) (U K : ℕ) : ℕ :=
  ((oddUniverse U).filter (fun v => degree v < K)).card

/-- All signature levels and both resource pools are monotone in one common
profile. This guarantees that one vertex order works for every degree cutoff. -/
def DegreeProfileMonotone {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → ℕ → ℕ) : Prop :=
  ∀ s : ℕ, s ≤ ps.length →
  ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U, profile u ≤ profile v →
    evenDegree s u ≤ evenDegree s v ∧ wholeDegree s u ≤ wholeDegree s v

/-- Meaning of the integer degrees: two distinct endpoints with the same
signature and both degrees at least `K` have at least `K` raw common neighbors. -/
def VertexDegreeBounds (L U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → ℕ → ℕ) : Prop :=
  ∀ s : ℕ, s ≤ ps.length → ∀ K : ℕ,
  ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U, u ≠ v →
    divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
    (K ≤ evenDegree s u → K ≤ evenDegree s v →
      K ≤ (rawCommon Nat.Coprime (evenUniverse L) u v).card) ∧
    (K ≤ wholeDegree s u → K ≤ wholeDegree s v →
      K ≤ (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card)

/-- Histogram certificate. The two low-count tests may use different cutoffs,
but their degree functions are ultimately sorted by the same profile. -/
def DegreeIntervalCertificate (U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → ℕ → ℕ) : Prop :=
  ∀ b : ℕ, b ≤ halfOdds U - retainedOdds U →
  ∀ j : ℕ, 1 ≤ j → j ≤ maxHalfLength U →
    ∃ s : ℕ, s ≤ ps.length ∧ signatureBudget s < j ∧
      (lowDegreeCount (evenDegree s) U (b + j) ≤
          b + (j - signatureBudget s - 1) / 2 ∨
       lowDegreeCount (wholeDegree s) U (U - threshold U + maxHalfLength U + j) ≤
          b + (j - signatureBudget s - 1) / 2)

/-- A histogram bound supplies the exact cardinality-defined good prefix and
its strict exceptional-gap budget. -/
theorem degree_prefix_of_low_count
    (O : List ℕ) (hO : O.Nodup) (U : ℕ) (hOset : O.toFinset = oddUniverse U)
    (degree : ℕ → ℕ) (hsorted : O.Pairwise (fun u v => degree v ≤ degree u))
    {b j h K : ℕ} (hh : h < j)
    (hcount : lowDegreeCount degree U K ≤ b + (j - h - 1) / 2) :
    ∃ p : ℕ, p ≤ halfOdds U ∧
      2 * (halfOdds U - p - b) + h < j ∧
      orderPrefix O p = (oddUniverse U).filter (fun v => K ≤ degree v) := by
  classical
  let R := lowDegreeCount degree U K
  let p := halfOdds U - R
  have hR : R ≤ halfOdds U := by
    have hc := Finset.card_le_card
      (Finset.filter_subset (fun v => degree v < K) (oddUniverse U))
    simpa only [oddUniverse_card, R, lowDegreeCount] using hc
  have hOlen : O.length = halfOdds U := by
    simpa only [hOset, oddUniverse_card] using (List.toFinset_card_of_nodup hO).symm
  refine ⟨p, Nat.sub_le _ _, ?_, ?_⟩
  · change R ≤ b + (j - h - 1) / 2 at hcount
    dsimp only [p]
    omega
  · simpa only [hOlen, hOset, lowDegreeCount, R, p] using
      profile_orderPrefix_eq_filter degree O K hO hsorted

/-- One descending common-profile order turns the two integer degree histograms
into the exact-prefix interval certificate. -/
theorem exact_interval_of_degree_certificate {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (L U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → ℕ → ℕ)
    (hmono : DegreeProfileMonotone profile U ps evenDegree wholeDegree)
    (hdegree : VertexDegreeBounds L U ps evenDegree wholeDegree)
    (hcert : DegreeIntervalCertificate U ps evenDegree wholeDegree) :
    ∃ O : List ℕ, O.Nodup ∧ O.toFinset = oddUniverse U ∧
      ExactIntervalCertificate L U O ps := by
  classical
  obtain ⟨O, hO, hOset, hsorted, _hprefix⟩ :=
    exists_profile_order_all_thresholds profile (oddUniverse U)
  have hmem : ∀ u ∈ O, u ∈ oddUniverse U := by
    intro u hu
    rw [← hOset]
    exact List.mem_toFinset.mpr hu
  refine ⟨O, hO, hOset, ?_⟩
  intro b hb j hj hjU
  obtain ⟨s, hs, hsj, he | hr⟩ := hcert b hb j hj hjU
  · have hsortedE : O.Pairwise (fun u v => evenDegree s v ≤ evenDegree s u) := by
      apply List.Pairwise.imp_of_mem _ hsorted
      intro u v hu hv huv
      exact (hmono s hs v (hmem v hv) u (hmem u hu) huv).1
    obtain ⟨p, hp, hbudget, hP⟩ :=
      degree_prefix_of_low_count O hO U hOset (evenDegree s) hsortedE hsj he
    refine ⟨s, hs, p, hp, hbudget, Or.inl ?_⟩
    intro u hu v hv hne heq
    rw [hP] at hu hv
    rcases Finset.mem_filter.mp hu with ⟨huU, huK⟩
    rcases Finset.mem_filter.mp hv with ⟨hvU, hvK⟩
    exact (hdegree s hs (b + j) u huU v hvU hne heq).1 huK hvK
  · have hsortedR : O.Pairwise (fun u v => wholeDegree s v ≤ wholeDegree s u) := by
      apply List.Pairwise.imp_of_mem _ hsorted
      intro u v hu hv huv
      exact (hmono s hs v (hmem v hv) u (hmem u hu) huv).2
    obtain ⟨p, hp, hbudget, hP⟩ :=
      degree_prefix_of_low_count O hO U hOset (wholeDegree s) hsortedR hsj hr
    refine ⟨s, hs, p, hp, hbudget, Or.inr ?_⟩
    intro u hu v hv hne heq
    rw [hP] at hu hv
    rcases Finset.mem_filter.mp hu with ⟨huU, huK⟩
    rcases Finset.mem_filter.mp hv with ⟨hvU, hvK⟩
    exact (hdegree s hs (U - threshold U + maxHalfLength U + j)
      u huU v hvU hne heq).2 huK hvK

/-- Soundness of the range test used by a maximum-range or deque certificate.
This is an arithmetic implication, independent of any algorithm implementation. -/
theorem degree_range_implies_disjunction
    (RE RR : ℕ → ℕ) (j bmax a D : ℕ)
    (hrange : ∀ z : ℕ, j ≤ z → z ≤ j + bmax →
      z < j + RR (D + j) - a → RE z + j ≤ z + a) :
    ∀ b : ℕ, b ≤ bmax → RE (b + j) ≤ b + a ∨ RR (D + j) ≤ b + a := by
  intro b hb
  by_cases hR : RR (D + j) ≤ b + a
  · exact Or.inr hR
  · left
    have hE := hrange (b + j) (by omega) (by omega) (by omega)
    omega

/-- The generic histogram criterion yields the required odd cycle throughout
its interval, using the proved endpoint principle. -/
theorem degree_interval_criterion_sound {β : Type*} [LinearOrder β]
    (profile : ℕ → β) {L U : ℕ} (hL : 6 ≤ L) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → ℕ → ℕ)
    (hmono : DegreeProfileMonotone profile U ps evenDegree wholeDegree)
    (hdegree : VertexDegreeBounds L U ps evenDegree wholeDegree)
    (hcert : DegreeIntervalCertificate U ps evenDegree wholeDegree)
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  obtain ⟨O, hO, hOset, hinterval⟩ :=
    exact_interval_of_degree_certificate profile L U ps evenDegree wholeDegree hmono hdegree hcert
  exact exact_interval_criterion_with_proved_endpoints hL O ps hO hOset hinterval
    hLn hnU A hA hdense hk hkn

#print axioms degree_prefix_of_low_count
#print axioms exact_interval_of_degree_certificate
#print axioms degree_range_implies_disjunction
#print axioms degree_interval_criterion_sound

end Erdos883Verified
