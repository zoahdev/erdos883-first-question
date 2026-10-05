import Erdos883AKEndpoints
import Erdos883ProfileOrder

namespace Erdos883Verified

/-- Strict low-profile count; equal-threshold vertices remain usable. -/
def lowProfileCount {β : Type*} [LinearOrder β] (profile : ℕ → β)
    (U : ℕ) (z : β) : ℕ := ((oddUniverse U).filter (fun v => profile v < z)).card

/-- Univariate certificate with explicit integer lower-degree functions. -/
def ProfileIntervalCertificate {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (valid : β → Prop) (_L U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → β → ℕ) : Prop :=
  ∀ b : ℕ, b ≤ halfOdds U - retainedOdds U →
  ∀ j : ℕ, 1 ≤ j → j ≤ maxHalfLength U →
    ∃ s : ℕ, s ≤ ps.length ∧ ∃ z : β, valid z ∧
      2 * (lowProfileCount profile U z - b) + signatureBudget s < j ∧
      (b + j ≤ evenDegree s z ∨ U - threshold U + maxHalfLength U + j ≤ wholeDegree s z)

/-- The actual raw-neighbor lower bounds needed to give meaning to degree functions. -/
def ProfileDegreeBounds {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (valid : β → Prop) (L U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → β → ℕ) : Prop :=
  ∀ s : ℕ, s ≤ ps.length → ∀ z : β, valid z →
  ∀ u ∈ oddUniverse U, ∀ v ∈ oddUniverse U, u ≠ v →
    divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
    z ≤ profile u → z ≤ profile v →
    evenDegree s z ≤ (rawCommon Nat.Coprime (evenUniverse L) u v).card ∧
    wholeDegree s z ≤ (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card

/-- One descending profile order converts every rank's strict-profile certificate
into an exact-prefix interval certificate. -/
theorem exact_interval_of_profile_certificate {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (valid : β → Prop) (L U : ℕ) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → β → ℕ)
    (hdegree : ProfileDegreeBounds profile valid L U ps evenDegree wholeDegree)
    (hcert : ProfileIntervalCertificate profile valid L U ps evenDegree wholeDegree) :
    ∃ O : List ℕ, O.Nodup ∧ O.toFinset = oddUniverse U ∧
      ExactIntervalCertificate L U O ps := by
  classical
  obtain ⟨O, hO, hOset, hsorted, hprefix⟩ :=
    exists_profile_order_all_thresholds profile (oddUniverse U)
  have hOlen : O.length = halfOdds U := by
    simpa only [hOset, oddUniverse_card] using (List.toFinset_card_of_nodup hO).symm
  refine ⟨O, hO, hOset, ?_⟩
  intro b hb j hj hjU
  obtain ⟨s, hs, z, hz, hbudget, hres⟩ := hcert b hb j hj hjU
  let R := lowProfileCount profile U z
  let p := halfOdds U - R
  have hR : R ≤ halfOdds U := by
    have h := Finset.card_le_card (Finset.filter_subset (fun v => profile v < z) (oddUniverse U))
    simpa only [oddUniverse_card, R, lowProfileCount] using h
  have hp : p ≤ halfOdds U := Nat.sub_le _ _
  have hP : orderPrefix O p = (oddUniverse U).filter (fun v => z ≤ profile v) := by
    simpa only [hOlen, lowProfileCount, R, p] using (hprefix z).2.1
  refine ⟨s, hs, p, hp, ?_, ?_⟩
  · change 2 * (halfOdds U - p - b) + signatureBudget s < j
    change 2 * (R - b) + signatureBudget s < j at hbudget
    dsimp [p]
    omega
  · rcases hres with he | hr
    · left
      intro u hu v hv hne heq
      rw [hP] at hu hv
      rcases Finset.mem_filter.mp hu with ⟨huU, huz⟩
      rcases Finset.mem_filter.mp hv with ⟨hvU, hvz⟩
      exact he.trans (hdegree s hs z hz u huU v hvU hne heq huz hvz).1
    · right
      intro u hu v hv hne heq
      rw [hP] at hu hv
      rcases Finset.mem_filter.mp hu with ⟨huU, huz⟩
      rcases Finset.mem_filter.mp hv with ⟨hvU, hvz⟩
      exact hr.trans (hdegree s hs z hz u huU v hvU hne heq huz hvz).2

/-- Soundness of the candidate's profile-only interval reduction. -/
theorem profile_interval_criterion_sound {β : Type*} [LinearOrder β]
    (profile : ℕ → β) (valid : β → Prop) {L U : ℕ} (hL : 6 ≤ L) (ps : List ℕ)
    (evenDegree wholeDegree : ℕ → β → ℕ)
    (hdegree : ProfileDegreeBounds profile valid L U ps evenDegree wholeDegree)
    (hcert : ProfileIntervalCertificate profile valid L U ps evenDegree wholeDegree)
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  obtain ⟨O, hO, hOset, hinterval⟩ :=
    exact_interval_of_profile_certificate profile valid L U ps evenDegree wholeDegree hdegree hcert
  exact exact_interval_criterion_with_proved_endpoints hL O ps hO hOset hinterval
    hLn hnU A hA hdense hk hkn

#print axioms exact_interval_of_profile_certificate
#print axioms profile_interval_criterion_sound
end Erdos883Verified
