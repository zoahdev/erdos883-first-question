import Erdos883AdaptiveSpanRowsAppend

namespace Erdos883Verified

/-- A structural proof list, indexed separately by span and row chunks.
Its entries are the exact numeric certificates already checked by the kernel. -/
inductive NumericChunkProofs (L W c d : ℕ) :
    List (List AdaptiveNumericSpan) → List (List AdaptiveProfileRow) → Prop
  | nil : NumericChunkProofs L W c d [] []
  | cons {spans rows spanChunks rowChunks}
      (head : coreNumericSpansCheck L W c d spans rows = true)
      (tail : NumericChunkProofs L W c d spanChunks rowChunks) :
      NumericChunkProofs L W c d (spans :: spanChunks) (rows :: rowChunks)

theorem NumericChunkProofs.sound {L W c d : ℕ}
    {spanChunks : List (List AdaptiveNumericSpan)}
    {rowChunks : List (List AdaptiveProfileRow)}
    (h : NumericChunkProofs L W c d spanChunks rowChunks) :
    coreNumericSpansCheck L W c d spanChunks.flatten rowChunks.flatten = true := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      exact coreNumericSpansCheck_append head ih

/-- Explicit target views avoid normalization of concrete filtered row lists. -/
theorem coreNumericSpansCheck_of_chunkProofs {L W c d : ℕ}
    (spans : List AdaptiveNumericSpan) (rows : List AdaptiveProfileRow)
    (spanChunks : List (List AdaptiveNumericSpan))
    (rowChunks : List (List AdaptiveProfileRow))
    (hspans : spans = spanChunks.flatten)
    (hrows : rows = rowChunks.flatten)
    (hchecks : NumericChunkProofs L W c d spanChunks rowChunks) :
    coreNumericSpansCheck L W c d spans rows = true := by
  rw [hspans, hrows]
  exact hchecks.sound

#print axioms NumericChunkProofs.sound
#print axioms coreNumericSpansCheck_of_chunkProofs
end Erdos883Verified
