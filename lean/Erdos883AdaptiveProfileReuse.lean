import Erdos883AdaptiveCertificateProfiles

namespace Erdos883Verified

/-- Restrict a once-certified master profile table to a smaller ambient size. -/
def adaptiveRowsThrough (U : ℕ) (rows : List AdaptiveProfileRow) : List AdaptiveProfileRow :=
  rows.filter (fun row => decide (row.value ≤ U))

theorem coreProfileOrderCheck_of_pairwise {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : rows.Pairwise (fun a b => a.profile ≤ b.profile)) :
    coreProfileOrderCheck rows = true := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    cases rows with
    | nil => rfl
    | cons b rows =>
      have hab := (List.pairwise_cons.mp horder).1 b (by simp)
      have ha := hvalid a (by simp)
      have hb := hvalid b (by simp)
      have hcross : a.numerator * b.value ≤ b.numerator * a.value := by
        have hrat := (div_le_div_iff₀ (Nat.cast_pos.mpr ha.1)
          (Nat.cast_pos.mpr hb.1)).mp hab
        exact_mod_cast hrat
      simp only [coreProfileOrderCheck, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hcross, ih (fun row hr => hvalid row (List.mem_cons_of_mem _ hr))
        (List.pairwise_cons.mp horder).2⟩

theorem adaptiveRowsThrough_valid {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows) (U : ℕ) :
    AdaptiveProfileRowsValid (adaptiveRowsThrough U rows) := by
  intro row hrow
  exact hvalid row (List.mem_filter.mp hrow).1

theorem adaptiveRowsThrough_order {rows : List AdaptiveProfileRow}
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true) (U : ℕ) :
    coreProfileOrderCheck (adaptiveRowsThrough U rows) = true := by
  apply coreProfileOrderCheck_of_pairwise (adaptiveRowsThrough_valid hvalid U)
  exact (coreProfileOrderCheck_sound hvalid horder).filter _

theorem coreProfileValues_rowsThrough (rows : List AdaptiveProfileRow) (U : ℕ) :
    coreProfileValues (adaptiveRowsThrough U rows) =
      (coreProfileValues rows).filter (fun v => decide (v ≤ U)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [adaptiveRowsThrough, List.filter_cons, coreProfileValues, List.map_cons] at ih ⊢
    split <;> simp_all

theorem adaptiveRowsThrough_permutation {rows : List AdaptiveProfileRow} {U V : ℕ}
    (hUV : U ≤ V)
    (hnd : (coreProfileValues rows).Nodup)
    (hset : (coreProfileValues rows).toFinset = oddUniverse V) :
    (coreProfileValues (adaptiveRowsThrough U rows)).Nodup ∧
      (coreProfileValues (adaptiveRowsThrough U rows)).toFinset = oddUniverse U := by
  rw [coreProfileValues_rowsThrough]
  refine ⟨hnd.filter _, ?_⟩
  rw [← List.filter_toFinset, hset]
  ext v
  simp only [oddUniverse, Finset.mem_filter, Finset.mem_Icc, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hv1, _hvV⟩, hvodd⟩, hvU⟩
    exact ⟨⟨hv1, hvU⟩, hvodd⟩
  · rintro ⟨⟨hv1, hvU⟩, hvodd⟩
    exact ⟨⟨⟨hv1, hvU.trans hUV⟩, hvodd⟩, hvU⟩

/-- All semantic and Boolean order properties are inherited from the master
certificate; no repeated factorization, primality, sorting or permutation
computation is needed for a smaller U. -/
theorem adaptiveRowsThrough_certified {rows : List AdaptiveProfileRow} {U V : ℕ}
    (hUV : U ≤ V)
    (hvalid : AdaptiveProfileRowsValid rows)
    (horder : coreProfileOrderCheck rows = true)
    (hnd : (coreProfileValues rows).Nodup)
    (hset : (coreProfileValues rows).toFinset = oddUniverse V) :
    AdaptiveProfileRowsValid (adaptiveRowsThrough U rows) ∧
    coreProfileOrderCheck (adaptiveRowsThrough U rows) = true ∧
    (coreProfileValues (adaptiveRowsThrough U rows)).Nodup ∧
    (coreProfileValues (adaptiveRowsThrough U rows)).toFinset = oddUniverse U :=
  ⟨adaptiveRowsThrough_valid hvalid U, adaptiveRowsThrough_order hvalid horder U,
    adaptiveRowsThrough_permutation hUV hnd hset⟩

#print axioms coreProfileOrderCheck_of_pairwise
#print axioms adaptiveRowsThrough_valid
#print axioms adaptiveRowsThrough_order
#print axioms coreProfileValues_rowsThrough
#print axioms adaptiveRowsThrough_permutation
#print axioms adaptiveRowsThrough_certified
end Erdos883Verified
