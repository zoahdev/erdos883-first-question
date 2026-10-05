import CanonicalTarget
import Erdos883IntervalHelpers
import Erdos883Skeleton
import Erdos883RelationResources

namespace Erdos883Verified

/-- The coprime-endpoint property initially invoked through AK1996.
It is proved elementarily in Erdos883AKEndpoints; this definition is not an axiom. -/
def OddEndpointPrinciple : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ Y : Finset ℕ, Y ⊆ oddUniverse n →
    retainedOdds n ≤ Y.card →
    ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧ Nat.Coprime a b

def signatureBudget (s : ℕ) : ℕ := if s = 0 then 0 else 2 ^ s + 1

/-- Pointwise form of the manuscript's exact interval minima certificate.
Raw coprimality counts include 1 before skeleton deletion. -/
def ExactIntervalCertificate (L U : ℕ) (O ps : List ℕ) : Prop :=
  ∀ b : ℕ, b ≤ halfOdds U - retainedOdds U →
  ∀ j : ℕ, 1 ≤ j → j ≤ maxHalfLength U →
    ∃ s : ℕ, s ≤ ps.length ∧ ∃ p : ℕ, p ≤ halfOdds U ∧
      2 * (halfOdds U - p - b) + signatureBudget s < j ∧
      ((∀ u ∈ orderPrefix O p, ∀ v ∈ orderPrefix O p, u ≠ v →
          divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
          b + j ≤ (rawCommon Nat.Coprime (evenUniverse L) u v).card) ∨
       (∀ u ∈ orderPrefix O p, ∀ v ∈ orderPrefix O p, u ≠ v →
          divisorSignatureCode (ps.take s) u = divisorSignatureCode (ps.take s) v →
          U - threshold U + maxHalfLength U + j ≤
            (rawCommon Nat.Coprime (Finset.Icc 1 L) u v).card))

/-- Soundness of the all-subsets finite interval criterion. The endpoint principle
and the arithmetic interval certificate are explicit hypotheses of this interface. -/
theorem exact_interval_criterion_sound
    (hAK : OddEndpointPrinciple) {L U : ℕ} (hL : 6 ≤ L)
    (O ps : List ℕ) (hO : O.Nodup) (hOset : O.toFinset = oddUniverse U)
    (hcert : ExactIntervalCertificate L U O ps)
    {n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hdense : threshold n < A.card)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ maxHalfLength n) :
    2 * k + 1 ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  classical
  let b := (evenUniverse n \ A).card
  let selected := A ∩ oddUniverse n
  have hselected : selected ⊆ O.toFinset := by
    rw [hOset]
    exact (Finset.inter_subset_right).trans (oddUniverse_mono hnU)
  have hsurplus : retainedOdds n + b ≤ selected.card :=
    dense_set_odd_surplus A hA hdense
  obtain ⟨Y, T, hYcard, hTb, hYS, hTS, hYO, hTO, hYT, hUnion, hSep, hPrefix⟩ :=
    exists_ordered_retention O selected (retainedOdds n) b hO hselected hsurplus
  have hYodd : Y ⊆ oddUniverse n := hYS.trans Finset.inter_subset_right
  have hYA : Y ⊆ A := hYS.trans Finset.inter_subset_left
  obtain ⟨a, ha, z, hz, haz, hac⟩ :=
    hAK n (hL.trans hLn) Y hYodd (by omega)
  have hYsize : k + 1 ≤ Y.card := by
    have h := retained_ge n
    omega
  obtain ⟨o, ho, hoY, hoFirst, hoLast, hoTrans, hoZero⟩ :=
    exists_divisor_skeleton Y ps a z k ha hz haz hk hYsize
  have hoA : ∀ i, o i ∈ A := fun i => hYA (hoY i)
  have hclose : (SimpleGraph.fromRel Nat.Coprime).Adj (o (Fin.last k)) (o 0) := by
    rw [hoLast, hoFirst, SimpleGraph.fromRel_adj]
    exact ⟨haz.symm, Or.inl hac.symm⟩
  have hEven : Disjoint (evenUniverse L) (Finset.univ.image o) := by
    apply Finset.disjoint_left.mpr
    intro v hv he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    rcases (Finset.mem_filter.mp hv).2 with ⟨x, hx⟩
    rcases (Finset.mem_filter.mp (hYodd (hoY i))).2 with ⟨y, hy⟩
    omega
  have hb : (evenUniverse L \ A).card ≤ b := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨evenUniverse_mono hLn (Finset.mem_sdiff.mp hx).1,
      (Finset.mem_sdiff.mp hx).2⟩
  have hcost := interval_whole_pool_cost A hLn hnU hA hdense hkn o ho
  change 2 * k + 1 ∈ ((SimpleGraph.fromRel Nat.Coprime).induce (A : Set ℕ)).oddCycleLengths
  apply induced_oddCycle_of_relation_pool_certificates Nat.Coprime A
    (evenUniverse L) (Finset.Icc 1 L) (b := b)
    (cost := U - threshold U + maxHalfLength U) hk o ho hoA hclose hEven hb hcost
  intro j hj hjk
  have hbU : b ≤ halfOdds U - retainedOdds U :=
    (dense_missing_even_bound A hA hdense).trans (missing_even_bound_mono hnU)
  have hjU : j ≤ maxHalfLength U := by
    unfold maxHalfLength at hkn ⊢
    omega
  obtain ⟨s, hs, p, hp, hbudget, hresources⟩ := hcert b hbU j hj hjU
  let P := orderPrefix O p
  let B : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => o i ∉ P)
  let cross := signatureTransitionGaps (fun i => divisorSignatureCode (ps.take s) (o i))
  have hOlen : O.length = halfOdds U := by
    simpa only [hOset, oddUniverse_card] using (List.toFinset_card_of_nodup hO).symm
  have hpLen : p ≤ O.length := by omega
  have hB : B.card ≤ halfOdds U - p - b := by
    calc
      B.card ≤ (Y \ P).card := skeleton_outside_card_le o ho Y P hoY
      _ ≤ (O.toFinset \ P).card - b := hPrefix p
      _ = halfOdds U - p - b := by
        rw [outside_orderPrefix_card O hO hpLen, hOlen]
  have hcross : cross.card ≤ signatureBudget s := by
    by_cases hs0 : s = 0
    · subst s
      simpa [signatureBudget, cross] using hoZero.le
    · simpa only [signatureBudget, if_neg hs0] using hoTrans s hs
  refine ⟨touchedGaps B ∪ cross, exceptional_gap_budget B cross hB hcross hbudget, ?_⟩
  intro i hi
  have hgood : o i.castSucc ∈ P ∧ o i.succ ∈ P ∧
      divisorSignatureCode (ps.take s) (o i.castSucc) =
        divisorSignatureCode (ps.take s) (o i.succ) := by
    simpa only [Finset.mem_union, touchedGaps, cross, signatureTransitionGaps,
      Finset.mem_filter, Finset.mem_univ, true_and, B, not_or, not_not, and_assoc]
      using hi
  have hneq : o i.castSucc ≠ o i.succ := by
    apply ho.ne
    intro he
    have hv := congrArg Fin.val he
    dsimp at hv
    omega
  rcases hresources with he | hr
  · exact Or.inl (he _ hgood.1 _ hgood.2.1 hneq hgood.2.2)
  · exact Or.inr (hr _ hgood.1 _ hgood.2.1 hneq hgood.2.2)

#print axioms exact_interval_criterion_sound

/-- End-to-end reduction to an explicit endpoint principle and a covering
family of arithmetic interval certificates. -/
theorem firstQuestion_of_interval_cover
    (hAK : OddEndpointPrinciple)
    (hcover : ∀ n : ℕ, 6 ≤ n →
      ∃ L U : ℕ, ∃ O ps : List ℕ,
        6 ≤ L ∧ L ≤ n ∧ n ≤ U ∧ O.Nodup ∧
        O.toFinset = oddUniverse U ∧ ExactIntervalCertificate L U O ps) :
    Erdos883Target.FirstQuestion := by
  apply Erdos883Target.firstQuestion_iff_halfLength.mpr
  intro n A hA hdense k hk hkn
  have hn : 6 ≤ n := by omega
  obtain ⟨L, U, O, ps, hL, hLn, hnU, hO, hOset, hcert⟩ := hcover n hn
  exact exact_interval_criterion_sound hAK hL O ps hO hOset hcert hLn hnU A hA hdense hk hkn

#print axioms firstQuestion_of_interval_cover

end Erdos883Verified
