import Erdos883AdaptiveCertificateProfileCore
import Erdos883FactorizedProfiles

namespace Erdos883Verified

def AdaptiveProfileRow.Valid (row : AdaptiveProfileRow) : Prop :=
  0 < row.value ∧ row.numerator = Nat.totient row.value

def AdaptiveProfileRowsValid (rows : List AdaptiveProfileRow) : Prop :=
  ∀ row ∈ rows, row.Valid

def AdaptiveProfileRow.profile (row : AdaptiveProfileRow) : ℚ :=
  (row.numerator : ℚ) / (row.value : ℚ)

theorem coreProfileRowCheck_sound {row : AdaptiveProfileRow}
    (h : coreProfileRowCheck row = true) : row.Valid := by
  simp only [coreProfileRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2.2.2, coreDedup_eq, corePrimeSieveCount_eq]
  apply fastPrimeSieveCount_factorList_eq_totient h.1 h.2.1
  intro p hp
  exact corePrimeCheck_sound (List.all_eq_true.mp h.2.2.1 p hp)

theorem coreProfileMetadataCheck_sound {rows : List AdaptiveProfileRow}
    (h : coreProfileMetadataCheck rows = true) : AdaptiveProfileRowsValid rows := by
  intro row hrow
  exact coreProfileRowCheck_sound (List.all_eq_true.mp h row hrow)

theorem adaptiveProfileRowsValid_of_chunks {rows : List AdaptiveProfileRow} {C : ℕ}
    (chunks : Fin C → List AdaptiveProfileRow)
    (heq : (List.ofFn chunks).flatten = rows)
    (hvalid : ∀ i, AdaptiveProfileRowsValid (chunks i)) : AdaptiveProfileRowsValid rows := by
  intro row hrow
  rw [← heq] at hrow
  obtain ⟨chunk, hchunk, hrow⟩ := List.mem_flatten.mp hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchunk
  exact hvalid i row hrow

theorem AdaptiveProfileRow.profile_eq_totientDensity {row : AdaptiveProfileRow}
    (h : row.Valid) : row.profile = totientDensity row.value := by
  simp only [AdaptiveProfileRow.profile, totientDensity, h.2]

theorem adaptiveProfileRow_le_of_cross {a b : AdaptiveProfileRow}
    (ha : a.Valid) (hb : b.Valid)
    (h : a.numerator * b.value ≤ b.numerator * a.value) :
    a.profile ≤ b.profile := by
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr ha.1) (Nat.cast_pos.mpr hb.1)).mpr
  exact_mod_cast h

theorem coreProfileOrderCheck_sound {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows) (h : coreProfileOrderCheck rows = true) :
    rows.Pairwise (fun a b => a.profile ≤ b.profile) := by
  induction rows with
  | nil => exact List.Pairwise.nil
  | cons a rows ih =>
    cases rows with
    | nil => simp
    | cons b rows =>
      simp only [coreProfileOrderCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      have htail := ih (fun row hrow => hvalid row (List.mem_cons_of_mem _ hrow)) h.2
      have hab := adaptiveProfileRow_le_of_cross (hvalid a (by simp))
        (hvalid b (by simp)) h.1
      apply List.pairwise_cons.mpr
      refine ⟨?_, htail⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hab
      · exact hab.trans ((List.pairwise_cons.mp htail).1 c hc)

theorem coreProfileValues_pairwise {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows) (h : coreProfileOrderCheck rows = true) :
    (coreProfileValues rows).Pairwise (fun u v => totientDensity u ≤ totientDensity v) := by
  unfold coreProfileValues
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (coreProfileOrderCheck_sound hvalid h)
  intro a b ha hb hab
  simpa only [AdaptiveProfileRow.profile_eq_totientDensity (hvalid a ha),
    AdaptiveProfileRow.profile_eq_totientDensity (hvalid b hb)] using hab

/-- In an increasing degree list, at most the first `r` entries can lie below a
threshold already reached by entry `r`. This also handles tied degrees exactly. -/
theorem list_lowDegree_length_le_rank (degree : ℕ → ℕ) (O : List ℕ)
    (hsorted : O.Pairwise (fun u v => degree u ≤ degree v))
    {r K : ℕ} (hr : r < O.length) (hK : K ≤ degree O[r]) :
    (O.filter (fun v => decide (degree v < K))).length ≤ r := by
  induction O generalizing r with
  | nil => simp at hr
  | cons a O ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    cases r with
    | zero =>
      have hKa : K ≤ degree a := by simpa using hK
      have hempty : (a :: O).filter (fun v => decide (degree v < K)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro v hv hlt
        have hKv : K ≤ degree v := by
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hKa
          · exact hKa.trans (hhead v hv)
        exact (not_lt_of_ge hKv) (of_decide_eq_true hlt)
      simp [hempty]
    | succ r =>
      have hr' : r < O.length := by simpa using hr
      have hK' : K ≤ degree O[r] := by simpa using hK
      have hi := ih htail hr' hK'
      by_cases ha : degree a < K <;> simp [ha] <;> omega

theorem lowDegreeCount_le_rank (degree : ℕ → ℕ) {U : ℕ} (O : List ℕ)
    (hO : O.Nodup) (hset : O.toFinset = oddUniverse U)
    (hsorted : O.Pairwise (fun u v => degree u ≤ degree v))
    {r K : ℕ} (hr : r < O.length) (hK : K ≤ degree O[r]) :
    lowDegreeCount degree U K ≤ r := by
  unfold lowDegreeCount
  rw [← hset, List.filter_toFinset, List.toFinset_card_of_nodup (hO.filter _)]
  exact list_lowDegree_length_le_rank degree O hsorted hr hK

/-- The finite metadata proof can be split into independently reduced chunks. -/
theorem adaptiveProfileRowsValid_of_coreChunks {rows : List AdaptiveProfileRow} {C : ℕ}
    (chunks : Fin C → List AdaptiveProfileRow)
    (heq : (List.ofFn chunks).flatten = rows)
    (hchecks : ∀ i, coreProfileMetadataCheck (chunks i) = true) :
    AdaptiveProfileRowsValid rows :=
  adaptiveProfileRowsValid_of_chunks chunks heq
    (fun i => coreProfileMetadataCheck_sound (hchecks i))

/-- A checked increasing profile table gives a bound for every monotone
nonnegative-profile degree function by testing just its entry at rank `r`. -/
theorem profileLowDegreeCount_le_rank {rows : List AdaptiveProfileRow} {U : ℕ}
    (degree : ℚ → ℕ)
    (hmono : ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → degree x ≤ degree y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    {r K : ℕ} (hr : r < rows.length) (hK : K ≤ degree rows[r].profile) :
    lowDegreeCount (fun v => degree (totientDensity v)) U K ≤ r := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound hperm
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
    (coreProfileValues rows) hnd hset hsorted hr' hK'

/-- Total-list indexing for any monotone degree function. -/
theorem profileLowDegreeCount_le_rank_getD {rows : List AdaptiveProfileRow} {U : ℕ}
    (degree : ℚ → ℕ)
    (hmono : ∀ {x y : ℚ}, 0 ≤ x → x ≤ y → degree x ≤ degree y)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    {r K : ℕ} (hr : r < rows.length) (fallback : AdaptiveProfileRow)
    (hK : K ≤ degree (rows.getD r fallback).profile) :
    lowDegreeCount (fun v => degree (totientDensity v)) U K ≤ r := by
  apply profileLowDegreeCount_le_rank degree hmono hvalid horder hperm hr
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos rows r hr, Option.getD_some] using hK

/-- The adaptive degree function satisfies the monotonicity needed by a rank test. -/
theorem adaptiveLowDegreeCount_le_rank {rows : List AdaptiveProfileRow}
    {scale U W p : ℕ} (hp : 2 ≤ p)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    {r K : ℕ} (hr : r < rows.length)
    (hK : K ≤ adaptiveDegree scale U W p rows[r].profile) :
    lowDegreeCount (fun v => adaptiveDegree scale U W p (totientDensity v)) U K ≤ r :=
  profileLowDegreeCount_le_rank (adaptiveDegree scale U W p)
    (fun hx hxy => adaptiveDegree_mono scale U W hp hx hxy)
    hvalid horder hperm hr hK

/-- A total-list-index variant keeps pure certificate expressions proof-free. -/
theorem adaptiveLowDegreeCount_le_rank_getD {rows : List AdaptiveProfileRow}
    {scale U W p : ℕ} (hp : 2 ≤ p)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    {r K : ℕ} (hr : r < rows.length) (fallback : AdaptiveProfileRow)
    (hK : K ≤ adaptiveDegree scale U W p (rows.getD r fallback).profile) :
    lowDegreeCount (fun v => adaptiveDegree scale U W p (totientDensity v)) U K ≤ r := by
  apply adaptiveLowDegreeCount_le_rank hp hvalid horder hperm hr
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos rows r hr, Option.getD_some] using hK

/-- Ranks at or beyond the table length need no numeric degree check. -/
theorem lowDegreeCount_le_profileLength {rows : List AdaptiveProfileRow} {U r K : ℕ}
    (degree : ℕ → ℕ)
    (hperm : coreOrderPermutationCheck U (coreProfileValues rows) = true)
    (hr : rows.length ≤ r) : lowDegreeCount degree U K ≤ r := by
  obtain ⟨hnd, hset⟩ := coreOrderPermutationCheck_sound hperm
  have hc := Finset.card_le_card
    (Finset.filter_subset (fun v => degree v < K) (oddUniverse U))
  change lowDegreeCount degree U K ≤ _ at hc
  rw [← hset, List.toFinset_card_of_nodup hnd, coreProfileValues, List.length_map] at hc
  exact hc.trans hr

#print axioms profileLowDegreeCount_le_rank
#print axioms profileLowDegreeCount_le_rank_getD
#print axioms adaptiveLowDegreeCount_le_rank
#print axioms adaptiveLowDegreeCount_le_rank_getD
#print axioms lowDegreeCount_le_profileLength

#print axioms coreProfileRowCheck_sound
#print axioms coreProfileMetadataCheck_sound
#print axioms coreProfileOrderCheck_sound
#print axioms coreProfileValues_pairwise
#print axioms lowDegreeCount_le_rank

end Erdos883Verified
