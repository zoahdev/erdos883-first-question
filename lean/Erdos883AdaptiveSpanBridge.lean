import Erdos883AdaptiveSpanCore
import Erdos883AdaptiveCertificateAssembly

namespace Erdos883Verified

theorem AdaptiveSpanTree.leafBounds_left {lo hi m : Nat} {l r : AdaptiveSpanTree}
    {F : Nat → Nat} (h : (AdaptiveSpanTree.node lo hi m l r).LeafBounds F) :
    l.LeafBounds F := by
  intro sp hsp i hlo hhi
  exact h sp (List.mem_append_left _ hsp) i hlo hhi

theorem AdaptiveSpanTree.leafBounds_right {lo hi m : Nat} {l r : AdaptiveSpanTree}
    {F : Nat → Nat} (h : (AdaptiveSpanTree.node lo hi m l r).LeafBounds F) :
    r.LeafBounds F := by
  intro sp hsp i hlo hhi
  exact h sp (List.mem_append_right _ hsp) i hlo hhi

theorem AdaptiveSpanTree.cache_domain {t : AdaptiveSpanTree}
    (hc : t.cacheCheck = true) : t.low ≤ t.high := by
  induction t with
  | leaf lo hi m => exact of_decide_eq_true hc
  | node lo hi m l r hl hr =>
      simp only [cacheCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hld := hl hc.1.2
      have hrd := hr hc.2
      simp only [low, high]
      omega

/-- Cached minima are valid at every rank in the covered root interval. -/
theorem AdaptiveSpanTree.cache_sound {t : AdaptiveSpanTree} {F : Nat → Nat}
    (hc : t.cacheCheck = true) (hf : t.LeafBounds F)
    {i : Nat} (hlo : t.low ≤ i) (hhi : i ≤ t.high) : t.minimum ≤ F i := by
  induction t with
  | leaf lo hi m => exact hf ⟨lo, hi, m⟩ (by simp [spans]) i hlo hhi
  | node lo hi m l r hl hr =>
      simp only [cacheCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [low, high] at hlo hhi
      change m ≤ F i
      by_cases hil : i ≤ l.high
      · exact hc.1.1.2.2.2.1.trans
          (hl hc.1.2 (leafBounds_left hf) (by omega) hil)
      · exact hc.1.1.2.2.2.2.trans
          (hr hc.2 (leafBounds_right hf) (by omega) (by omega))

/-- The range checker is sound at every queried rank, with full leaf coverage. -/
theorem AdaptiveSpanTree.rangeGe_sound {t : AdaptiveSpanTree} {F : Nat → Nat}
    (hc : t.cacheCheck = true) (hf : t.LeafBounds F)
    {lo hi bound : Nat} (h : t.rangeGe lo hi bound = true)
    {i : Nat} (htlo : t.low ≤ i) (hthi : i ≤ t.high)
    (hlo : lo ≤ i) (hhi : i ≤ hi) : bound ≤ F i := by
  induction t with
  | leaf lidx hidx m =>
      have hm := cache_sound hc hf htlo hthi
      change decide (hi < lidx ∨ hidx < lo ∨ bound ≤ m) = true at h
      have hx := of_decide_eq_true h
      simp only [low, high, minimum] at htlo hthi hm
      omega
  | node lidx hidx m l r hl hr =>
      by_cases hx : hi < lidx ∨ hidx < lo ∨ bound ≤ m
      · have hm := cache_sound hc hf htlo hthi
        simp only [low, high, minimum] at htlo hthi hm
        omega
      · simp only [rangeGe, low, high, minimum, hx, ↓reduceIte, Bool.and_eq_true] at h
        simp only [cacheCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only [low, high] at htlo hthi
        by_cases hil : i ≤ l.high
        · exact hl hc.1.2 (leafBounds_left hf) h.1 (by omega) hil
        · exact hr hc.2 (leafBounds_right hf) h.2 (by omega) (by omega)

theorem AdaptiveSpanTree.rangeGe_sound_of_domain {t : AdaptiveSpanTree}
    {F : Nat → Nat} {n lo hi bound i : Nat}
    (hc : t.cacheCheck = true) (hd : t.domainCheck n = true)
    (hf : t.LeafBounds F) (h : t.rangeGe lo hi bound = true)
    (hiN : i < n) (hlo : lo ≤ i) (hhi : i ≤ hi) : bound ≤ F i := by
  have hd' := of_decide_eq_true hd
  exact rangeGe_sound hc hf h (by omega) (by omega) hlo hhi

/-- Arithmetic for the split witness, with span-tree bounds rather than one
leaf per rank. The two functions need not be monotone for this theorem. -/
theorem adaptiveSpanRankWitnessCheck_sound
    {H n bmax D j h : Nat} {w : AdaptiveRankWitness}
    {even whole : AdaptiveSpanTree} {E R : Nat → Nat}
    (hcE : even.cacheCheck = true) (hcR : whole.cacheCheck = true)
    (hdE : even.domainCheck n = true) (hdR : whole.domainCheck n = true)
    (hfE : even.LeafBounds (fun i => E i + H - i))
    (hfR : whole.LeafBounds R)
    (hc : adaptiveSpanRankWitnessCheck H bmax D j h w even whole = true)
    {b : Nat} (hb : b ≤ bmax)
    (hrE : b + (j-h-1)/2 < n) (hrR : w.split + (j-h-1)/2 < n)
    (hrank : b + (j-h-1)/2 ≤ H) :
    h < j ∧ (b < w.split → b+j ≤ E (b + (j-h-1)/2)) ∧
      (w.split ≤ b → D+j ≤ R (w.split + (j-h-1)/2)) := by
  simp only [adaptiveSpanRankWitnessCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hh, hs⟩, he, hr⟩
  refine ⟨hh, ?_, ?_⟩
  · intro hbs
    have hs0 : w.split ≠ 0 := by omega
    simp only [hs0, ↓reduceIte] at he
    have hge := even.rangeGe_sound_of_domain hcE hdE hfE he hrE (by omega) (by omega)
    omega
  · intro hsb
    have hneq : w.split ≠ bmax+1 := by omega
    simp only [hneq, ↓reduceIte] at hr
    exact whole.rangeGe_sound_of_domain hcR hdR hfR hr hrR (by omega) (by omega)

/-- Semantic link to a sorted profile table. The fallback is irrelevant within
the checked root domain, but keeps certificate expressions proof-free. -/
def AdaptiveSpanTreeRepresents (rows : List AdaptiveProfileRow) (H : Nat)
    (E R : ℚ → Nat) (even whole : AdaptiveSpanTree) : Prop :=
  even.domainCheck rows.length = true ∧ whole.domainCheck rows.length = true ∧
    even.LeafBounds (fun i => E (rows.getD i ⟨1, [], 1⟩).profile + H - i) ∧
    whole.LeafBounds (fun i => R (rows.getD i ⟨1, [], 1⟩).profile)

/-- A semantic permutation hypothesis supports separately checked chunk sorts
and merges instead of re-running a whole-table sort. -/
theorem profileLowDegreeCount_le_rank_of_permutation
    {rows : List AdaptiveProfileRow} {U : Nat}
    (degree : ℚ → Nat)
    (hmono : ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → degree x ≤ degree y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U)
    {r K : Nat} (hr : r < rows.length) (hK : K ≤ degree rows[r].profile) :
    lowDegreeCount (fun v => degree (totientDensity v)) U K ≤ r := by
  have hr' : r < (coreProfileValues rows).length := by
    simpa only [coreProfileValues, List.length_map] using hr
  have hsorted : (coreProfileValues rows).Pairwise
      (fun u v => degree (totientDensity u) ≤ degree (totientDensity v)) := by
    apply List.Pairwise.imp _ (coreProfileValues_pairwise hvalid horder)
    intro u v huv
    exact hmono (totientDensity_nonneg u) huv
  have hK' : K ≤ degree (totientDensity (coreProfileValues rows)[r]) := by
    simpa only [coreProfileValues, List.getElem_map,
      AdaptiveProfileRow.profile_eq_totientDensity (hvalid rows[r] (List.getElem_mem hr))] using hK
  exact lowDegreeCount_le_rank (fun v => degree (totientDensity v))
    (coreProfileValues rows) hperm.1 hperm.2 hsorted hr' hK'

theorem profileLowDegreeCount_le_rank_getD_of_permutation
    {rows : List AdaptiveProfileRow} {U : Nat}
    (degree : ℚ → Nat)
    (hmono : ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → degree x ≤ degree y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U)
    {r K : Nat} (hr : r < rows.length) (fallback : AdaptiveProfileRow)
    (hK : K ≤ degree (rows.getD r fallback).profile) :
    lowDegreeCount (fun v => degree (totientDensity v)) U K ≤ r := by
  apply profileLowDegreeCount_le_rank_of_permutation degree hmono hvalid horder hperm hr
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos rows r hr, Option.getD_some] using hK

/-- Span certificates imply the same adaptive histogram criterion as a full
per-rank minimum tree, without computing a degree at every profile row. -/
theorem adaptive_histogram_of_span_tree_witnesses {rows : List AdaptiveProfileRow} {U : Nat}
    (ps : List Nat) (E R : Nat → ℚ → Nat)
    (hmonoE : ∀ s ≤ ps.length, ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → E s x ≤ E s y)
    (hmonoR : ∀ s ≤ ps.length, ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → R s x ≤ R s y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U)
    (hsize : halfOdds U - retainedOdds U + 1 + maxHalfLength U / 2 < rows.length)
    (trees : Nat → AdaptiveSpanTree × AdaptiveSpanTree)
    (hcache : ∀ s ≤ ps.length,
      (trees s).1.cacheCheck = true ∧ (trees s).2.cacheCheck = true)
    (hrep : ∀ s ≤ ps.length, AdaptiveSpanTreeRepresents rows (halfOdds U)
      (E s) (R s) (trees s).1 (trees s).2)
    (witness : Nat → AdaptiveRankWitness)
    (hcheck : ∀ j, 1 ≤ j → j ≤ maxHalfLength U →
      (witness j).s ≤ ps.length ∧
      adaptiveSpanRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
        (U - threshold U + maxHalfLength U) j (signatureBudget (witness j).s)
        (witness j) (trees (witness j).s).1 (trees (witness j).s).2 = true) :
    DegreeIntervalCertificate U ps
      (fun s v => E s (totientDensity v)) (fun s v => R s (totientDensity v)) := by
  have hlength : rows.length = halfOdds U := by
    obtain ⟨hnd, hset⟩ := hperm
    have hc := List.toFinset_card_of_nodup hnd
    rw [hset, oddUniverse_card] at hc
    simpa only [coreProfileValues, List.length_map] using hc.symm
  intro b hb j hj hjU
  let w := witness j
  let a := (j - signatureBudget w.s - 1) / 2
  obtain ⟨hs, hc⟩ := hcheck j hj hjU
  change w.s ≤ ps.length at hs
  have hca := hc
  simp only [adaptiveSpanRankWitnessCheck, Bool.and_eq_true, decide_eq_true_eq] at hca
  have hsj : signatureBudget w.s < j := hca.1.1
  have ht : w.split ≤ halfOdds U - retainedOdds U + 1 := hca.1.2
  have ha : a ≤ maxHalfLength U / 2 := by dsimp [a]; omega
  have hrE : b + a < rows.length := by omega
  have hrR : w.split + a < rows.length := by omega
  obtain ⟨hdE, hdR, hfE, hfR⟩ := hrep w.s hs
  have htcheck := adaptiveSpanRankWitnessCheck_sound (hcache w.s hs).1
    (hcache w.s hs).2 hdE hdR hfE hfR hc hb hrE hrR
    (by change b+a ≤ halfOdds U; omega)
  refine ⟨w.s, hs, hsj, ?_⟩
  by_cases hbt : b < w.split
  · left
    exact profileLowDegreeCount_le_rank_getD_of_permutation (E w.s) (hmonoE w.s hs)
      hvalid horder hperm hrE ⟨1, [], 1⟩ (htcheck.2.1 hbt)
  · right
    have hR := profileLowDegreeCount_le_rank_getD_of_permutation (R w.s) (hmonoR w.s hs)
      hvalid horder hperm hrR ⟨1, [], 1⟩ (htcheck.2.2 (by change w.split ≤ b; omega))
    exact hR.trans (by omega)

/-- Check a finite witness table once and obtain all queried rank statements. -/
theorem adaptiveSpanWitnessTable_sound {U plen : Nat}
    (trees : Nat → AdaptiveSpanTree × AdaptiveSpanTree) (ws : List AdaptiveRankWitness)
    (hlen : ws.length = maxHalfLength U)
    (hchecks : (ws.zipIdx).all (fun (w,i) => decide (w.s ≤ plen) &&
      adaptiveSpanRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
        (U - threshold U + maxHalfLength U) (i+1) (signatureBudget w.s)
        w (trees w.s).1 (trees w.s).2) = true) :
    ∀ j, 1 ≤ j → j ≤ maxHalfLength U →
      (ws.getD (j-1) ⟨0,0⟩).s ≤ plen ∧
      adaptiveSpanRankWitnessCheck (halfOdds U) (halfOdds U - retainedOdds U)
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

#print axioms AdaptiveSpanTree.rangeGe_sound
#print axioms adaptive_histogram_of_span_tree_witnesses
#print axioms adaptiveSpanWitnessTable_sound

end Erdos883Verified
