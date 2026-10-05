import Erdos883AdaptiveCertificateData
import Erdos883SharpAdaptiveDegrees
namespace Erdos883Verified

def AdaptiveTreeRepresents (rows : List AdaptiveProfileRow) (H : Nat)
    (E R : ℚ → ℕ) (even whole : AdaptiveMinTree) : Prop :=
  ∀ r : Nat, ∀ hr : r < rows.length,
    (r, E rows[r].profile + H - r) ∈ even.entries ∧
    (r, R rows[r].profile) ∈ whole.entries

/-- A compressed rank witness proves the histogram disjunction simultaneously
for every discarded-odd count. -/
theorem adaptive_histogram_of_tree_witnesses {rows : List AdaptiveProfileRow} {U : Nat}
    (ps : List Nat) (E R : Nat → ℚ → Nat)
    (hmonoE : ∀ s ≤ ps.length, ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → E s x ≤ E s y)
    (hmonoR : ∀ s ≤ ps.length, ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → R s x ≤ R s y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    (hsize : halfOdds U - retainedOdds U + 1 + maxHalfLength U / 2 < rows.length)
    (trees : Nat → AdaptiveMinTree × AdaptiveMinTree)
    (hcache : ∀ s ≤ ps.length,
      (trees s).1.cacheCheck = true ∧ (trees s).2.cacheCheck = true)
    (hrep : ∀ s ≤ ps.length, AdaptiveTreeRepresents rows (halfOdds U)
      (E s) (R s) (trees s).1 (trees s).2)
    (witness : Nat → AdaptiveRankWitness)
    (hcheck : ∀ j, 1 ≤ j → j ≤ maxHalfLength U →
      (witness j).s ≤ ps.length ∧
      adaptiveRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
        (U - threshold U + maxHalfLength U) j (signatureBudget (witness j).s)
        (witness j) (trees (witness j).s).1 (trees (witness j).s).2 = true) :
    DegreeIntervalCertificate U ps
      (fun s v => E s (totientDensity v)) (fun s v => R s (totientDensity v)) := by
  have hlength : rows.length = halfOdds U := by
    obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound hperm
    have hc := List.toFinset_card_of_nodup hnd
    rw [hset, oddUniverse_card] at hc
    simpa only [coreProfileValues, List.length_map] using hc.symm
  intro b hb j hj hjU
  let w := witness j
  let a := (j - signatureBudget w.s - 1) / 2
  obtain ⟨hs, hc⟩ := hcheck j hj hjU
  change w.s ≤ ps.length at hs
  have hca := hc
  simp only [adaptiveRankWitnessCheck, Bool.and_eq_true, decide_eq_true_eq] at hca
  have hsj : signatureBudget w.s < j := hca.1.1
  have ht : w.split ≤ halfOdds U - retainedOdds U + 1 := hca.1.2
  have ha : a ≤ maxHalfLength U / 2 := by dsimp [a]; omega
  have hrE : b + a < rows.length := by omega
  have hrR : w.split + a < rows.length := by omega
  have he := (hrep w.s hs (b+a) hrE).1
  have hr := (hrep w.s hs (w.split+a) hrR).2
  have htcheck := adaptiveRankWitnessCheck_sound (hcache w.s hs).1 (hcache w.s hs).2 hc
    hb he hr (by change b+a ≤ halfOdds U; omega)
  refine ⟨w.s, hs, hsj, ?_⟩
  by_cases hbt : b < w.split
  · left
    apply profileLowDegreeCount_le_rank (E w.s) (hmonoE w.s hs) hvalid horder hperm hrE
    exact htcheck.2.1 hbt
  · right
    have hR := profileLowDegreeCount_le_rank (R w.s) (hmonoR w.s hs)
      hvalid horder hperm hrR (htcheck.2.2 (by change w.split ≤ b; omega))
    exact hR.trans (by omega)


theorem adaptiveTreeRepresents_of_entries {rows : List AdaptiveProfileRow}
    (L W c d H : Nat) (hvalid : AdaptiveProfileRowsValid rows) (hd : 0 < d)
    (even whole : AdaptiveMinTree)
    (hE : even.entries = coreDegreeEntries (L/2) W c d H true rows)
    (hR : whole.entries = coreDegreeEntries L W c d H false rows) :
    AdaptiveTreeRepresents rows H (sharpDegree (L/2) W c d)
      (sharpDegree L W c d) even whole := by
  intro r hr
  have hp := (hvalid rows[r] (List.getElem_mem hr)).1
  constructor
  · rw [hE]
    have he := coreDegreeEntries_mem hr (L/2) W c d H true
    simpa only [Bool.true_eq, ↓reduceIte,
      coreNumericDegree_eq_sharpDegree _ _ _ _ _ _ hp hd, AdaptiveProfileRow.profile] using he
  · rw [hR]
    have he := coreDegreeEntries_mem hr L W c d H false
    simpa only [Bool.false_eq_true, ↓reduceIte,
      coreNumericDegree_eq_sharpDegree _ _ _ _ _ _ hp hd, AdaptiveProfileRow.profile] using he

/-- Turn the checked finite witness table into the bounded universal statement. -/
theorem adaptiveWitnessTable_sound {U plen : Nat}
    (trees : Nat → AdaptiveMinTree × AdaptiveMinTree) (ws : List AdaptiveRankWitness)
    (hlen : ws.length = maxHalfLength U)
    (hchecks : (ws.zipIdx).all (fun (w,i) => decide (w.s ≤ plen) &&
      adaptiveRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
        (U - threshold U + maxHalfLength U) (i+1) (signatureBudget w.s)
        w (trees w.s).1 (trees w.s).2) = true) :
    ∀ j, 1 ≤ j → j ≤ maxHalfLength U →
      (ws.getD (j-1) ⟨0,0⟩).s ≤ plen ∧
      adaptiveRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
        (U - threshold U + maxHalfLength U) j
        (signatureBudget (ws.getD (j-1) ⟨0,0⟩).s)
        (ws.getD (j-1) ⟨0,0⟩)
        (trees (ws.getD (j-1) ⟨0,0⟩).s).1
        (trees (ws.getD (j-1) ⟨0,0⟩).s).2 = true := by
  intro j hj hjU
  have hr : j-1 < ws.length := by omega
  have hmem : (ws[j-1],j-1) ∈ ws.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hr])
  have ht := List.all_eq_true.mp hchecks _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have hjpred : j-1+1=j := by omega
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
    Option.getD_some, hjpred] using ht

#print axioms adaptiveTreeRepresents_of_entries
#print axioms adaptiveWitnessTable_sound
#print axioms adaptive_histogram_of_tree_witnesses
end Erdos883Verified
