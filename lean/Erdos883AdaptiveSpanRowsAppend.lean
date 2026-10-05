import Erdos883AdaptiveSpanRows
namespace Erdos883Verified

theorem coreNumericSpansCheck_append {L W c d : Nat}
    {sa sb : List AdaptiveNumericSpan} {ra rb : List AdaptiveProfileRow}
    (ha : coreNumericSpansCheck L W c d sa ra = true)
    (hb : coreNumericSpansCheck L W c d sb rb = true) :
    coreNumericSpansCheck L W c d (sa ++ sb) (ra ++ rb) = true := by
  induction sa generalizing ra with
  | nil =>
    have hra : ra = [] := by simpa only [coreNumericSpansCheck, List.isEmpty_iff] using ha
    simpa only [hra, List.nil_append] using hb
  | cons sp sa ih =>
    simp only [coreNumericSpansCheck, Bool.and_eq_true, decide_eq_true_eq] at ha
    have hlen : sp.len ≤ ra.length := by
      have ht := ha.1.2.1
      rw [List.length_take] at ht
      omega
    have hhead : (ra ++ rb).headD adaptiveSpanFallback = ra.headD adaptiveSpanFallback := by
      cases ra with
      | nil => simp at hlen; have := ha.1.1; omega
      | cons x xs => rfl
    simp only [List.cons_append, coreNumericSpansCheck, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · simpa only [List.take_append_of_le_length hlen, hhead] using ha.1
    · rw [List.drop_append_of_le_length hlen]
      exact ih ha.2

/-- Independently checked row/span blocks compose without re-evaluating their data. -/
theorem coreNumericSpansCheck_pairedChunks {L W c d : Nat}
    (chunks : List (List AdaptiveNumericSpan × List AdaptiveProfileRow))
    (h : chunks.all (fun p => coreNumericSpansCheck L W c d p.1 p.2) = true) :
    coreNumericSpansCheck L W c d (chunks.flatMap Prod.fst) (chunks.flatMap Prod.snd) = true := by
  induction chunks with
  | nil => rfl
  | cons p chunks ih =>
    have hp : coreNumericSpansCheck L W c d p.1 p.2 = true :=
      List.all_eq_true.mp h p (by simp)
    have ht : chunks.all (fun p => coreNumericSpansCheck L W c d p.1 p.2) = true := by
      apply List.all_eq_true.mpr
      intro p hp
      exact List.all_eq_true.mp h p (List.mem_cons_of_mem _ hp)
    simpa only [List.flatMap_cons] using coreNumericSpansCheck_append hp (ih ht)
#print axioms coreNumericSpansCheck_append
#print axioms coreNumericSpansCheck_pairedChunks
end Erdos883Verified
