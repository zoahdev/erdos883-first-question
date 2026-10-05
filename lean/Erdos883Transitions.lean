import Mathlib.Data.Finset.Card

namespace Erdos883Verified

variable {α : Type*} [DecidableEq α]

/-- The cost of crossing from one signature to the next. -/
def signatureChange (a b : α) : ℕ := if a = b then 0 else 1

/-- Number of adjacent unequal signatures in a linear ordering. -/
def signatureTransitions : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: xs => signatureChange a b + signatureTransitions (b :: xs)

@[simp] theorem signatureTransitions_nil : signatureTransitions ([] : List α) = 0 := rfl

@[simp] theorem signatureTransitions_singleton (a : α) :
    signatureTransitions [a] = 0 := rfl

@[simp] theorem signatureTransitions_cons_cons (a b : α) (xs : List α) :
    signatureTransitions (a :: b :: xs) =
      signatureChange a b + signatureTransitions (b :: xs) := rfl

theorem signatureChange_le_one (a b : α) : signatureChange a b ≤ 1 := by
  simp only [signatureChange]
  split <;> omega

/-- Removing a middle signature cannot cost more than its two incident crossings. -/
theorem signatureChange_triangle (a b c : α) :
    signatureChange a c ≤ signatureChange a b + signatureChange b c := by
  by_cases hab : a = b
  · subst b
    simp [signatureChange]
  · by_cases hbc : b = c
    · subst c
      simp [signatureChange]
    · have hac := signatureChange_le_one a c
      simp only [signatureChange, if_neg hab, if_neg hbc]
      unfold signatureChange at hac
      omega

/-- Prepending one signature creates at most one additional transition. -/
theorem signatureTransitions_cons_le (a : α) (xs : List α) :
    signatureTransitions (a :: xs) ≤ signatureTransitions xs + 1 := by
  cases xs with
  | nil => simp
  | cons b xs =>
    rw [signatureTransitions_cons_cons]
    have h := signatureChange_le_one a b
    omega

/-- Deleting the first signature cannot increase the transition count. -/
theorem signatureTransitions_tail_le (a : α) (xs : List α) :
    signatureTransitions xs ≤ signatureTransitions (a :: xs) := by
  cases xs with
  | nil => simp
  | cons b xs =>
    rw [signatureTransitions_cons_cons]
    omega

/-- Appending one signature creates at most one additional transition. -/
theorem signatureTransitions_append_singleton_le (xs : List α) (a : α) :
    signatureTransitions (xs ++ [a]) ≤ signatureTransitions xs + 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    cases xs with
    | nil => simpa using signatureChange_le_one b a
    | cons c xs =>
      simp only [List.cons_append, signatureTransitions_cons_cons] at ih ⊢
      omega

/-- Deleting an arbitrary entry cannot increase the transition count. -/
theorem signatureTransitions_delete_at_split (xs ys : List α) (a : α) :
    signatureTransitions (xs ++ ys) ≤ signatureTransitions (xs ++ a :: ys) := by
  induction xs with
  | nil =>
    simpa using signatureTransitions_tail_le a ys
  | cons b xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp
      | cons c ys =>
        simp only [List.cons_append, List.nil_append, signatureTransitions_cons_cons]
        have h := signatureChange_triangle b a c
        omega
    | cons c xs =>
      simp only [List.cons_append, signatureTransitions_cons_cons] at ih ⊢
      omega

/-- Adding two prescribed endpoints costs at most two transitions. -/
theorem signatureTransitions_add_endpoints_le (xs : List α) (a b : α) :
    signatureTransitions (a :: (xs ++ [b])) ≤ signatureTransitions xs + 2 := by
  have h₁ := signatureTransitions_cons_le a (xs ++ [b])
  have h₂ := signatureTransitions_append_singleton_le xs b
  omega

/-- Deleting two specified occurrences, wherever they lie, cannot increase transitions. -/
theorem signatureTransitions_delete_two_at_splits (xs ys zs : List α) (a b : α) :
    signatureTransitions (xs ++ ys ++ zs) ≤
      signatureTransitions (xs ++ a :: (ys ++ b :: zs)) := by
  have h₁ := signatureTransitions_delete_at_split xs (ys ++ b :: zs) a
  have h₂ := signatureTransitions_delete_at_split (xs ++ ys) zs b
  simp only [List.append_assoc] at h₂ ⊢
  exact Nat.le_trans h₂ h₁

/-- Moving two specified occurrences to the start and end creates at most two
additional transitions. No sorting or contiguity hypothesis is needed. -/
theorem signatureTransitions_move_to_endpoints_le
    (xs ys zs : List α) (a b : α) :
    signatureTransitions (a :: ((xs ++ ys ++ zs) ++ [b])) ≤
      signatureTransitions (xs ++ a :: (ys ++ b :: zs)) + 2 := by
  have h₁ := signatureTransitions_add_endpoints_le (xs ++ ys ++ zs) a b
  have h₂ := signatureTransitions_delete_two_at_splits xs ys zs a b
  omega

/-- Concatenating two lists introduces at most one boundary transition. -/
theorem signatureTransitions_append_le (xs ys : List α) :
    signatureTransitions (xs ++ ys) ≤
      signatureTransitions xs + signatureTransitions ys + 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simpa using signatureTransitions_cons_le a ys
    | cons b xs =>
      simp only [List.cons_append, signatureTransitions_cons_cons] at ih ⊢
      omega

/-- A constant block has no transitions. -/
@[simp] theorem signatureTransitions_replicate (n : ℕ) (a : α) :
    signatureTransitions (List.replicate n a) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.replicate_succ, signatureTransitions_cons_cons] at ih ⊢
      simpa [signatureChange] using ih

/-- An explicitly block-contiguous ordering has at most one transition per
boundary between blocks. This does not assert existence of such an ordering. -/
theorem signatureTransitions_blocks_le (labels : List α) (multiplicity : α → ℕ) :
    signatureTransitions (labels.flatMap (fun a => List.replicate (multiplicity a) a)) ≤
      labels.length - 1 := by
  induction labels with
  | nil => simp
  | cons a labels ih =>
    cases labels with
    | nil => simp
    | cons b labels =>
      rw [List.flatMap_cons]
      have h := signatureTransitions_append_le (List.replicate (multiplicity a) a)
        ((b :: labels).flatMap (fun a => List.replicate (multiplicity a) a))
      simp only [signatureTransitions_replicate, List.length_cons] at ih h ⊢
      omega

/-- When every named block is nonempty, its signatures are exactly the labels. -/
theorem signatureBlocks_toFinset (labels : List α) (multiplicity : α → ℕ)
    (hpos : ∀ a ∈ labels, 0 < multiplicity a) :
    (labels.flatMap (fun a => List.replicate (multiplicity a) a)).toFinset =
      labels.toFinset := by
  ext a
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨b, hb, _, rfl⟩
    exact hb
  · intro ha
    exact ⟨a, ha, Nat.ne_of_gt (hpos a ha), rfl⟩

/-- A list explicitly presented as one nonempty constant block per distinct
signature has at most its number of distinct signatures minus one transitions. -/
theorem signatureTransitions_distinct_blocks_le
    (labels : List α) (multiplicity : α → ℕ)
    (hlabels : labels.Nodup) (hpos : ∀ a ∈ labels, 0 < multiplicity a) :
    signatureTransitions (labels.flatMap (fun a => List.replicate (multiplicity a) a)) ≤
      (labels.flatMap (fun a => List.replicate (multiplicity a) a)).toFinset.card - 1 := by
  rw [signatureBlocks_toFinset labels multiplicity hpos,
    List.toFinset_card_of_nodup hlabels]
  exact signatureTransitions_blocks_le labels multiplicity

#print axioms signatureTransitions_nil
#print axioms signatureTransitions_singleton
#print axioms signatureTransitions_cons_cons
#print axioms signatureChange_le_one
#print axioms signatureChange_triangle
#print axioms signatureTransitions_cons_le
#print axioms signatureTransitions_tail_le
#print axioms signatureTransitions_append_singleton_le
#print axioms signatureTransitions_delete_at_split
#print axioms signatureTransitions_add_endpoints_le
#print axioms signatureTransitions_delete_two_at_splits
#print axioms signatureTransitions_move_to_endpoints_le

#print axioms signatureTransitions_append_le
#print axioms signatureTransitions_replicate
#print axioms signatureTransitions_blocks_le
#print axioms signatureBlocks_toFinset
#print axioms signatureTransitions_distinct_blocks_le

end Erdos883Verified
