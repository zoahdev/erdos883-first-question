import Erdos883AdaptiveSpanRowsCore
import Erdos883AdaptiveCertificateProfiles
import Erdos883SharpAdaptiveDegrees
import Erdos883AdaptiveSpanBridge

namespace Erdos883Verified

/-- A sorted profile at any valid rank is at least the profile at its head. -/
theorem adaptiveProfile_head_le_getD {rows : List AdaptiveProfileRow}
    (hsorted : rows.Pairwise (fun a b => a.profile ≤ b.profile))
    {i : ℕ} (hi : i < rows.length) :
    (rows.headD adaptiveSpanFallback).profile ≤ (rows.getD i adaptiveSpanFallback).profile := by
  cases rows with
  | nil => simp at hi
  | cons a rows =>
    cases i with
    | zero =>
      change a.profile ≤ a.profile
      exact le_rfl
    | succ i =>
      have hi' : i < rows.length := by simpa using hi
      rw [List.headD_cons, List.getD_cons_succ]
      have hg : rows.getD i adaptiveSpanFallback = rows[i] := by
        rw [List.getD_eq_getElem?_getD, getElem?_pos rows i hi']
        rfl
      rw [hg]
      exact (List.pairwise_cons.mp hsorted).1 rows[i] (List.getElem_mem hi')

/-- Completeness of the streaming partition is independently certified. -/
theorem coreNumericSpansCheck_length {L W c d : ℕ}
    {spans : List AdaptiveNumericSpan} {rows : List AdaptiveProfileRow}
    (h : coreNumericSpansCheck L W c d spans rows = true) :
    (spans.map (·.len)).sum = rows.length := by
  induction spans generalizing rows with
  | nil =>
    cases rows with
    | nil => rfl
    | cons row rows => simp [coreNumericSpansCheck] at h
  | cons sp spans ih =>
    simp only [coreNumericSpansCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := h.1.2.1
    rw [List.length_take] at hl
    have hi := ih h.2
    simp only [List.map_cons, List.sum_cons, hi, List.length_drop]
    omega

/-- Bounds for all ranks in every certified span, retaining absolute rank offsets.
 The even correction uses the span's final rank, so it remains a lower bound
 after subtracting any earlier rank in the span. -/
theorem coreNumericSpansCheck_bounds {L W c d : ℕ} (hd : 0 < d)
    {spans : List AdaptiveNumericSpan} {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows)
    (hsorted : rows.Pairwise (fun a b => a.profile ≤ b.profile))
    (hcheck : coreNumericSpansCheck L W c d spans rows = true)
    (H start : ℕ) :
    (∀ sp ∈ coreEvenSpans H start spans, ∀ i, sp.lo ≤ i → i ≤ sp.hi →
      start ≤ i ∧ i < start + rows.length ∧
      sp.minimum ≤ sharpDegree (L / 2) W c d
        (rows.getD (i-start) adaptiveSpanFallback).profile + H - i) ∧
    (∀ sp ∈ coreWholeSpans start spans, ∀ i, sp.lo ≤ i → i ≤ sp.hi →
      start ≤ i ∧ i < start + rows.length ∧
      sp.minimum ≤ sharpDegree L W c d
        (rows.getD (i-start) adaptiveSpanFallback).profile) := by
  induction spans generalizing rows start with
  | nil => simp [coreEvenSpans, coreWholeSpans]
  | cons sp spans ih =>
    simp only [coreNumericSpansCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck.1 with ⟨hlenpos, htake, hnum, hden, heven, hwhole⟩
    have hlen : sp.len ≤ rows.length := by rw [List.length_take] at htake; omega
    have hhead : (rows.headD adaptiveSpanFallback).Valid := by
      cases rows with
      | nil => simp at hlen; omega
      | cons row rows => exact hvalid row (by simp)
    have heq : sp.evenDegree = sharpDegree (L/2) W c d
        (rows.headD adaptiveSpanFallback).profile := by
      rw [heven, hnum, hden]
      exact coreNumericDegree_eq_sharpDegree _ _ _ _ _ _ hhead.1 hd
    have hrq : sp.wholeDegree = sharpDegree L W c d
        (rows.headD adaptiveSpanFallback).profile := by
      rw [hwhole, hnum, hden]
      exact coreNumericDegree_eq_sharpDegree _ _ _ _ _ _ hhead.1 hd
    have htailvalid : AdaptiveProfileRowsValid (rows.drop sp.len) := by
      intro row hr
      exact hvalid row (List.mem_of_mem_drop hr)
    have ht := ih htailvalid hsorted.drop hcheck.2 (start + sp.len)
    have hget (i : ℕ) (hi : start + sp.len ≤ i) :
        (rows.drop sp.len).getD (i-(start+sp.len)) adaptiveSpanFallback =
          rows.getD (i-start) adaptiveSpanFallback := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [show sp.len + (i - (start + sp.len)) = i - start by omega]
    constructor
    · intro leaf hleaf i hlo hhi
      rcases List.mem_cons.mp hleaf with rfl | hleaf
      · dsimp only at hlo hhi ⊢
        have hi : i-start < rows.length := by omega
        have hm := sharpDegree_mono (L/2) W c d
          (show 0 ≤ (rows.headD adaptiveSpanFallback).profile from
            div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (adaptiveProfile_head_le_getD hsorted hi)
        rw [← heq] at hm
        exact ⟨hlo, by omega, by omega⟩
      · obtain ⟨hlo', hhi', hb⟩ := ht.1 leaf hleaf i hlo hhi
        rw [hget i hlo'] at hb
        rw [List.length_drop] at hhi'
        exact ⟨by omega, by omega, hb⟩
    · intro leaf hleaf i hlo hhi
      rcases List.mem_cons.mp hleaf with rfl | hleaf
      · dsimp only at hlo hhi ⊢
        have hi : i-start < rows.length := by omega
        have hm := sharpDegree_mono L W c d
          (show 0 ≤ (rows.headD adaptiveSpanFallback).profile from
            div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (adaptiveProfile_head_le_getD hsorted hi)
        rw [← hrq] at hm
        exact ⟨hlo, by omega, hm⟩
      · obtain ⟨hlo', hhi', hb⟩ := ht.2 leaf hleaf i hlo hhi
        rw [hget i hlo'] at hb
        rw [List.length_drop] at hhi'
        exact ⟨by omega, by omega, hb⟩

/-- Ready-to-use leaf semantics for an even/whole span-tree pair. -/
theorem adaptiveSpanLeafBounds_of_numericCheck {L W c d H : ℕ} (hd : 0 < d)
    {spans : List AdaptiveNumericSpan} {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hcheck : coreNumericSpansCheck L W c d spans rows = true)
    (even whole : AdaptiveSpanTree)
    (heven : even.spans = coreEvenSpans H 0 spans)
    (hwhole : whole.spans = coreWholeSpans 0 spans) :
    even.LeafBounds (fun i => sharpDegree (L/2) W c d
      (rows.getD i adaptiveSpanFallback).profile + H - i) ∧
    whole.LeafBounds (fun i => sharpDegree L W c d
      (rows.getD i adaptiveSpanFallback).profile) := by
  have hb := coreNumericSpansCheck_bounds hd hvalid
    (coreProfileOrderCheck_sound hvalid horder) hcheck H 0
  constructor
  · intro sp hsp i hlo hhi
    rw [heven] at hsp
    simpa only [Nat.sub_zero] using (hb.1 sp hsp i hlo hhi).2.2
  · intro sp hsp i hlo hhi
    rw [hwhole] at hsp
    simpa only [Nat.sub_zero] using (hb.2 sp hsp i hlo hhi).2.2

/-- A checked numeric partition and checked root domains supply the complete
representation input expected by the span histogram assembly theorem. -/
theorem adaptiveSpanTreeRepresents_of_numericCheck {L W c d H : ℕ} (hd : 0 < d)
    {spans : List AdaptiveNumericSpan} {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hcheck : coreNumericSpansCheck L W c d spans rows = true)
    (even whole : AdaptiveSpanTree)
    (heven : even.spans = coreEvenSpans H 0 spans)
    (hwhole : whole.spans = coreWholeSpans 0 spans)
    (hdomEven : even.domainCheck rows.length = true)
    (hdomWhole : whole.domainCheck rows.length = true) :
    AdaptiveSpanTreeRepresents rows H (sharpDegree (L/2) W c d)
      (sharpDegree L W c d) even whole := by
  exact ⟨hdomEven, hdomWhole,
    adaptiveSpanLeafBounds_of_numericCheck hd hvalid horder hcheck even whole heven hwhole⟩

#print axioms adaptiveSpanTreeRepresents_of_numericCheck
#print axioms coreNumericSpansCheck_length
#print axioms coreNumericSpansCheck_bounds
#print axioms adaptiveSpanLeafBounds_of_numericCheck
end Erdos883Verified
