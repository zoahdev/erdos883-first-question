import Erdos883AdaptiveCertificateProfiles

namespace Erdos883Verified

/-- A independently checked chunk sort proves a permutation, for any fuel. -/
theorem coreSortCheck_perm {xs sorted : List Nat} {fuel : Nat}
    (h : coreSortFuel fuel xs = sorted) : xs.Perm sorted :=
  (coreSortFuel_perm fuel xs).symm.trans (List.Perm.of_eq h)

/-- A checked merge combines two previously proved chunk permutations. -/
theorem coreMergeCheck_perm {xs ys left right merged : List Nat} {fuel : Nat}
    (hl : xs.Perm left) (hr : ys.Perm right)
    (hm : coreMergeFuel fuel left right = merged) : (xs ++ ys).Perm merged :=
  (hl.append hr).trans ((coreMergeFuel_perm fuel left right).symm.trans
    (List.Perm.of_eq hm))

theorem adaptiveProfileSort_perm {rows : List AdaptiveProfileRow}
    {sorted : List Nat} {fuel : Nat}
    (h : coreSortFuel fuel (coreProfileValues rows) = sorted) :
    (coreProfileValues rows).Perm sorted := coreSortCheck_perm h

/-- Row-chunk append can be assembled without sorting the concatenated rows. -/
theorem adaptiveProfileMerge_perm {rowsLeft rowsRight : List AdaptiveProfileRow}
    {left right merged : List Nat} {fuel : Nat}
    (hl : (coreProfileValues rowsLeft).Perm left)
    (hr : (coreProfileValues rowsRight).Perm right)
    (hm : coreMergeFuel fuel left right = merged) :
    (coreProfileValues (rowsLeft ++ rowsRight)).Perm merged := by
  simpa only [coreProfileValues, List.map_append] using coreMergeCheck_perm hl hr hm

theorem adaptiveProfileValues_flatten (chunks : List (List AdaptiveProfileRow)) :
    coreProfileValues chunks.flatten = (chunks.map coreProfileValues).flatten := by
  simp only [coreProfileValues, List.map_flatten]
  rfl

theorem adaptiveProfileChunks_perm {chunks : List (List AdaptiveProfileRow)}
    {sorted : List Nat}
    (h : (chunks.map coreProfileValues).flatten.Perm sorted) :
    (coreProfileValues chunks.flatten).Perm sorted := by
  rw [adaptiveProfileValues_flatten]
  exact h

/-- Balanced merge nodes can retain their source as a list of chunks, so
assembly need not unfold the profile rows at every internal node. -/
theorem adaptiveProfileChunksMerge_perm
    {chunksLeft chunksRight : List (List AdaptiveProfileRow)}
    {left right merged : List Nat} {fuel : Nat}
    (hl : (chunksLeft.map coreProfileValues).flatten.Perm left)
    (hr : (chunksRight.map coreProfileValues).flatten.Perm right)
    (hm : coreMergeFuel fuel left right = merged) :
    ((chunksLeft ++ chunksRight).map coreProfileValues).flatten.Perm merged := by
  simpa only [List.map_append, List.flatten_append] using coreMergeCheck_perm hl hr hm

/-- Finish a chunked permutation certificate against the canonical odd range. -/
theorem coreOrderPermutation_of_range {U : Nat} {O : List Nat}
    (hperm : O.Perm (List.range' 1 (coreHalfOdds U) 2)) :
    O.Nodup ∧ O.toFinset = oddUniverse U := by
  refine ⟨hperm.nodup_iff.mpr (List.nodup_range' 2 (by decide)), ?_⟩
  ext v
  simp only [List.mem_toFinset, hperm.mem_iff, List.mem_range', oddUniverse,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold coreHalfOdds at hi
    exact ⟨⟨by omega, by omega⟩, ⟨i, by omega⟩⟩
  · rintro ⟨⟨hpos, hle⟩, ⟨i, hi⟩⟩
    refine ⟨i, ?_, by omega⟩
    unfold coreHalfOdds
    omega

theorem adaptiveProfilePermutation_of_range {rows : List AdaptiveProfileRow} {U : Nat}
    (hperm : (coreProfileValues rows).Perm (List.range' 1 (coreHalfOdds U) 2)) :
    (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U :=
  coreOrderPermutation_of_range hperm

/-- A flattened family of profile chunks is the whole odd universe once its
independently certified merge tree ends at the canonical odd range. -/
theorem adaptiveProfileChunksPermutation_of_range
    {chunks : List (List AdaptiveProfileRow)} {rows : List AdaptiveProfileRow} {U : Nat}
    (heq : chunks.flatten = rows)
    (hperm : (chunks.map coreProfileValues).flatten.Perm
      (List.range' 1 (coreHalfOdds U) 2)) :
    (coreProfileValues rows).Nodup ∧
      (coreProfileValues rows).toFinset = oddUniverse U := by
  subst rows
  exact adaptiveProfilePermutation_of_range (adaptiveProfileChunks_perm hperm)

#print axioms coreMergeCheck_perm
#print axioms adaptiveProfileChunksPermutation_of_range

end Erdos883Verified
