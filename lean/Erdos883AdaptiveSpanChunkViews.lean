import Erdos883AdaptiveSpanRowsAppend

namespace Erdos883Verified

/-- Structural assembly through explicit views. The target keeps `spans` and
`rows` opaque while the two list identities are proved separately; applying
this theorem does not compare expanded filtered row data by reduction. -/
theorem coreNumericSpansCheck_pairedChunks_of_eq {L W c d : ℕ}
    (spans : List AdaptiveNumericSpan) (rows : List AdaptiveProfileRow)
    (chunks : List (List AdaptiveNumericSpan × List AdaptiveProfileRow))
    (hspans : spans = chunks.flatMap Prod.fst)
    (hrows : rows = chunks.flatMap Prod.snd)
    (hchecks : chunks.all (fun p => coreNumericSpansCheck L W c d p.1 p.2) = true) :
    coreNumericSpansCheck L W c d spans rows = true := by
  rw [hspans, hrows]
  exact coreNumericSpansCheck_pairedChunks chunks hchecks

#print axioms coreNumericSpansCheck_pairedChunks_of_eq
end Erdos883Verified
