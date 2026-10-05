import Erdos883SortedSignatures
import Erdos883ExceptionalGaps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn

namespace Erdos883Verified

variable {α : Type*} [DecidableEq α]

/-- The linear path gaps across which the vertex signature changes. -/
def signatureTransitionGaps {k : ℕ} (sig : Fin (k + 1) → α) : Finset (Fin k) :=
  Finset.univ.filter (fun i => sig i.castSucc ≠ sig i.succ)

@[simp] theorem mem_signatureTransitionGaps {k : ℕ}
    (sig : Fin (k + 1) → α) (i : Fin k) :
    i ∈ signatureTransitionGaps sig ↔ sig i.castSucc ≠ sig i.succ := by
  simp [signatureTransitionGaps]

/-- Splitting a finite predicate at its first index splits its cardinality. -/
theorem card_filter_fin_succ {k : ℕ} (p : Fin (k + 1) → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      (if p 0 then 1 else 0) + (Finset.univ.filter (fun i : Fin k => p i.succ)).card := by
  rw [Fin.univ_succ, Finset.filter_cons, apply_ite Finset.card,
    Finset.card_cons, Finset.filter_map, Finset.card_map]
  split_ifs <;> simp [Nat.add_comm]

/-- The finite gap set and the list transition counter count the same crossings. -/
theorem signatureTransitionGaps_card {k : ℕ} (sig : Fin (k + 1) → α) :
    (signatureTransitionGaps sig).card = signatureTransitions (List.ofFn sig) := by
  induction k with
  | zero => simp [signatureTransitionGaps, List.ofFn_succ]
  | succ k ih =>
    unfold signatureTransitionGaps
    rw [card_filter_fin_succ]
    rw [List.ofFn_succ]
    conv_rhs => arg 1; arg 2; rw [List.ofFn_succ]
    rw [signatureTransitions_cons_cons]
    have htail := ih (fun i => sig i.succ)
    rw [List.ofFn_succ] at htail
    simp only [signatureTransitionGaps] at htail
    rw [← htail]
    by_cases h : sig 0 = sig 1 <;> simp [signatureChange, h]

/-- A list-based transition estimate transfers verbatim to the finite path gaps. -/
theorem signatureTransitionGaps_card_le_iff {k h : ℕ}
    (sig : Fin (k + 1) → α) :
    (signatureTransitionGaps sig).card ≤ h ↔
      signatureTransitions (List.ofFn sig) ≤ h := by
  rw [signatureTransitionGaps_card]

/-- The bridge specialized to a list accessed through its bounded getter. -/
theorem signatureTransitionGaps_get_card (xs : List α) {k : ℕ}
    (hlen : xs.length = k + 1) :
    (signatureTransitionGaps (fun i => xs.get (Fin.cast hlen.symm i))).card =
      signatureTransitions xs := by
  rw [signatureTransitionGaps_card]
  have hlist : List.ofFn (fun i => xs.get (Fin.cast hlen.symm i)) = xs := by
    rw [← List.ofFn_congr hlen xs.get, List.ofFn_get]
  rw [hlist]

/-- The finite exceptional-gap set inherits the sorted-signature bound. -/
theorem signatureTransitionGaps_sorted_card_le {k : ℕ}
    (sig : Fin (k + 1) → ℕ) (M : ℕ)
    (hsorted : (List.ofFn sig).Pairwise (· ≤ ·))
    (hbound : ∀ i, sig i < M) :
    (signatureTransitionGaps sig).card ≤ M - 1 := by
  rw [signatureTransitionGaps_card]
  apply signatureTransitions_sorted_lt _ M hsorted
  exact List.forall_mem_ofFn_iff.mpr hbound

/-- A bounded monotone finite signature sequence has at most `M - 1` crossings. -/
theorem signatureTransitionGaps_monotone_card_le {k : ℕ}
    (sig : Fin (k + 1) → ℕ) (M : ℕ)
    (hmono : Monotone sig) (hbound : ∀ i, sig i < M) :
    (signatureTransitionGaps sig).card ≤ M - 1 := by
  apply signatureTransitionGaps_sorted_card_le sig M _ hbound
  rw [List.pairwise_ofFn]
  intro i j hij
  exact hmono (le_of_lt hij)

/-- Any list transition bound supplies the crossing term in the rankwise
 exceptional-gap budget. -/
theorem exceptional_gap_budget_of_transitions {k R b h j : ℕ}
    (B : Finset (Fin (k + 1))) (sig : Fin (k + 1) → α)
    (hB : B.card ≤ R - b)
    (hsig : signatureTransitions (List.ofFn sig) ≤ h)
    (hbudget : 2 * (R - b) + h < j) :
    (touchedGaps B ∪ signatureTransitionGaps sig).card < j := by
  apply exceptional_gap_budget B (signatureTransitionGaps sig) hB _ hbudget
  rwa [signatureTransitionGaps_card]

/-- Vertex-level endpoint bounds transfer to the actual finite path gaps.
 The equality records how the indexed path is obtained from the moved list. -/
theorem signatureTransitionGaps_move_endpoints_card_le
    {V : Type*} {k : ℕ} (full : V → ℕ)
    (xs ys zs : List V) (a b : V) (d M : ℕ)
    (path : Fin (k + 1) → V)
    (hpath : List.ofFn path = a :: ((xs ++ ys ++ zs) ++ [b]))
    (hsorted : (xs ++ a :: (ys ++ b :: zs)).Pairwise
      (fun u v => full u ≤ full v))
    (hbound : ∀ v ∈ xs ++ a :: (ys ++ b :: zs), full v / d < M) :
    (signatureTransitionGaps (fun i => full (path i) / d)).card ≤ M + 1 := by
  rw [signatureTransitionGaps_card, List.ofFn_comp' path (fun v => full v / d), hpath]
  exact quotientSignatures_move_endpoints_le full xs ys zs a b d M hsorted hbound

#print axioms card_filter_fin_succ
#print axioms mem_signatureTransitionGaps
#print axioms signatureTransitionGaps_card
#print axioms signatureTransitionGaps_card_le_iff
#print axioms signatureTransitionGaps_get_card
#print axioms signatureTransitionGaps_sorted_card_le
#print axioms signatureTransitionGaps_monotone_card_le
#print axioms exceptional_gap_budget_of_transitions
#print axioms signatureTransitionGaps_move_endpoints_card_le

end Erdos883Verified
