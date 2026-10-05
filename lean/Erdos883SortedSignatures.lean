import Erdos883Transitions
import Mathlib.Data.List.Sort

namespace Erdos883Verified

/-- A nondecreasing list uses at least one integer of its available range at
 each transition. This version retains the first signature in the estimate. -/
theorem head_add_signatureTransitions_le
    (a : ℕ) (xs : List ℕ) (upper : ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ a :: xs, x ≤ upper) :
    a + signatureTransitions (a :: xs) ≤ upper := by
  induction xs generalizing a with
  | nil => simpa using hbound a (by simp)
  | cons b xs ih =>
    have hab : a ≤ b := (List.pairwise_cons.mp hsorted).1 b (by simp)
    have htail := (List.pairwise_cons.mp hsorted).2
    have htail_bound : ∀ x ∈ b :: xs, x ≤ upper := by
      intro x hx
      exact hbound x (List.mem_cons_of_mem a hx)
    have h := ih b htail htail_bound
    rw [signatureTransitions_cons_cons]
    by_cases heq : a = b
    · simp only [signatureChange, if_pos heq]
      omega
    · simp only [signatureChange, if_neg heq]
      omega

/-- At most `M - 1` changes occur in a nondecreasing list whose entries are
 natural-number signatures below `M`. The empty list is allowed, even for `M = 0`. -/
theorem signatureTransitions_sorted_lt
    (xs : List ℕ) (M : ℕ)
    (hsorted : xs.Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ xs, x < M) :
    signatureTransitions xs ≤ M - 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    have h := head_add_signatureTransitions_le a xs (M - 1) hsorted (by
      intro x hx
      have := hbound x hx
      omega)
    omega

/-- Moving two occurrences of a sorted bounded signature list to prescribed
 endpoints leaves at most `M + 1` transitions. -/
theorem signatureTransitions_move_sorted_endpoints_le
    (xs ys zs : List ℕ) (a b M : ℕ)
    (hsorted : (xs ++ a :: (ys ++ b :: zs)).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ xs ++ a :: (ys ++ b :: zs), x < M) :
    signatureTransitions (a :: ((xs ++ ys ++ zs) ++ [b])) ≤ M + 1 := by
  have hM : 0 < M := by
    have := hbound a (by simp)
    omega
  have hsorted_bound := signatureTransitions_sorted_lt
    (xs ++ a :: (ys ++ b :: zs)) M hsorted hbound
  have hmoved := signatureTransitions_move_to_endpoints_le xs ys zs a b
  omega

/-- Sorting by a full natural-number signature fixes one vertex ordering. -/
def fullSignatureOrder {V : Type*} (full : V → ℕ) (xs : List V) : List V :=
  xs.mergeSort (fun u v => decide (full u ≤ full v))

/-- Sorting preserves every occurrence, including vertices with tied signatures. -/
theorem fullSignatureOrder_perm {V : Type*} (full : V → ℕ) (xs : List V) :
    (fullSignatureOrder full xs).Perm xs := by
  exact List.mergeSort_perm xs _

/-- The one full-signature ordering is nondecreasing in its full code. -/
theorem fullSignatureOrder_pairwise {V : Type*} (full : V → ℕ) (xs : List V) :
    (fullSignatureOrder full xs).Pairwise (fun u v => full u ≤ full v) := by
  unfold fullSignatureOrder
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun u v => decide (full u ≤ full v))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs

/-- Every quotient of a nondecreasing full code is nondecreasing in the same
 vertex ordering. A denominator of zero is harmless, since all quotients are zero. -/
theorem quotientSignatures_pairwise {V : Type*} (full : V → ℕ)
    (xs : List V) (d : ℕ)
    (hsorted : xs.Pairwise (fun u v => full u ≤ full v)) :
    (xs.map (fun v => full v / d)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact hsorted.imp (fun h => Nat.div_le_div_right h)

/-- Every bounded quotient signature has few transitions in the same ordering. -/
theorem quotientSignatures_transitions_le {V : Type*} (full : V → ℕ)
    (xs : List V) (d M : ℕ)
    (hsorted : xs.Pairwise (fun u v => full u ≤ full v))
    (hbound : ∀ v ∈ xs, full v / d < M) :
    signatureTransitions (xs.map (fun v => full v / d)) ≤ M - 1 := by
  apply signatureTransitions_sorted_lt _ M
    (quotientSignatures_pairwise full xs d hsorted)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact hbound v hv

/-- Sorting once makes all bounded quotient signatures simultaneously have few
 transitions. The denominator and signature bound can vary after sorting. -/
theorem fullSignatureOrder_all_quotient_bounds {V : Type*}
    (full : V → ℕ) (xs : List V) :
    ∀ d M : ℕ, (∀ v ∈ xs, full v / d < M) →
      signatureTransitions
        ((fullSignatureOrder full xs).map (fun v => full v / d)) ≤ M - 1 := by
  intro d M hbound
  apply quotientSignatures_transitions_le full _ d M
    (fullSignatureOrder_pairwise full xs)
  intro v hv
  exact hbound v ((fullSignatureOrder_perm full xs).mem_iff.mp hv)

/-- Vertex-level version of the endpoint estimate. Only the full signatures
 need be sorted; every chosen quotient inherits the needed ordering. -/
theorem quotientSignatures_move_endpoints_le {V : Type*}
    (full : V → ℕ) (xs ys zs : List V) (a b : V) (d M : ℕ)
    (hsorted : (xs ++ a :: (ys ++ b :: zs)).Pairwise
      (fun u v => full u ≤ full v))
    (hbound : ∀ v ∈ xs ++ a :: (ys ++ b :: zs), full v / d < M) :
    signatureTransitions
      ((a :: ((xs ++ ys ++ zs) ++ [b])).map (fun v => full v / d)) ≤ M + 1 := by
  have hmap_sorted := quotientSignatures_pairwise full
    (xs ++ a :: (ys ++ b :: zs)) d hsorted
  have hmap_bound : ∀ x ∈ (xs ++ a :: (ys ++ b :: zs)).map (fun v => full v / d),
      x < M := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact hbound v hv
  simp only [List.map_append, List.map_cons] at hmap_sorted hmap_bound
  have h := signatureTransitions_move_sorted_endpoints_le
    (xs.map (fun v => full v / d)) (ys.map (fun v => full v / d))
    (zs.map (fun v => full v / d)) (full a / d) (full b / d) M
    hmap_sorted hmap_bound
  simpa only [List.map_append, List.map_cons, List.map_nil] using h

/-- An `r`-bit natural-number code has an initial `t`-bit quotient below `2^t`.
 This is a numerical fact; it does not assume or assert a prime-signature encoding. -/
theorem binaryPrefixQuotient_lt (code r t : ℕ) (ht : t ≤ r)
    (hcode : code < 2 ^ r) : code / 2 ^ (r - t) < 2 ^ t := by
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).2
  rw [← Nat.pow_add, Nat.add_sub_of_le ht]
  exact hcode

/-- All binary-prefix quotients have their expected transition bound after a
 single full-code sort. -/
theorem fullSignatureOrder_binaryPrefix_bounds {V : Type*}
    (full : V → ℕ) (xs : List V) (r : ℕ)
    (hbound : ∀ v ∈ xs, full v < 2 ^ r) :
    ∀ t ≤ r, signatureTransitions ((fullSignatureOrder full xs).map
      (fun v => full v / 2 ^ (r - t))) ≤ 2 ^ t - 1 := by
  intro t ht
  apply fullSignatureOrder_all_quotient_bounds full xs
  intro v hv
  exact binaryPrefixQuotient_lt (full v) r t ht (hbound v hv)

/-- The binary-prefix bounds survive moving two vertex occurrences to the
 endpoints, simultaneously for every prefix length. -/
theorem binaryPrefixQuotient_move_endpoints_le {V : Type*}
    (full : V → ℕ) (xs ys zs : List V) (a b : V) (r : ℕ)
    (hsorted : (xs ++ a :: (ys ++ b :: zs)).Pairwise
      (fun u v => full u ≤ full v))
    (hbound : ∀ v ∈ xs ++ a :: (ys ++ b :: zs), full v < 2 ^ r) :
    ∀ t ≤ r, signatureTransitions
      ((a :: ((xs ++ ys ++ zs) ++ [b])).map
        (fun v => full v / 2 ^ (r - t))) ≤ 2 ^ t + 1 := by
  intro t ht
  apply quotientSignatures_move_endpoints_le full xs ys zs a b _ _ hsorted
  intro v hv
  exact binaryPrefixQuotient_lt (full v) r t ht (hbound v hv)

/-- The zero-length prefix is identically zero. Hence its transition count
 is exactly zero in every ordering, without any sorting hypothesis. -/
theorem zeroPrefixQuotient_transitions_eq_zero {V : Type*}
    (full : V → ℕ) (xs : List V) (r : ℕ)
    (hbound : ∀ v ∈ xs, full v < 2 ^ r) :
    signatureTransitions (xs.map (fun v => full v / 2 ^ r)) = 0 := by
  have hmap : xs.map (fun v => full v / 2 ^ r) = xs.map (fun _ => 0) := by
    apply List.map_congr_left
    intro v hv
    exact Nat.div_eq_of_lt (hbound v hv)
  rw [hmap, List.map_const', signatureTransitions_replicate]

/-- In particular, the zero-length prefix in the full-signature ordering has
 exactly zero transitions, rather than merely satisfying the general upper bound. -/
theorem fullSignatureOrder_zeroPrefix_eq_zero {V : Type*}
    (full : V → ℕ) (xs : List V) (r : ℕ)
    (hbound : ∀ v ∈ xs, full v < 2 ^ r) :
    signatureTransitions ((fullSignatureOrder full xs).map
      (fun v => full v / 2 ^ r)) = 0 := by
  apply zeroPrefixQuotient_transitions_eq_zero full _ r
  intro v hv
  exact hbound v ((fullSignatureOrder_perm full xs).mem_iff.mp hv)

/-- Moving endpoints also preserves the exact zero-transition estimate for
 the zero-length prefix. -/
theorem zeroPrefixQuotient_move_endpoints_eq_zero {V : Type*}
    (full : V → ℕ) (xs ys zs : List V) (a b : V) (r : ℕ)
    (hbound : ∀ v ∈ xs ++ a :: (ys ++ b :: zs), full v < 2 ^ r) :
    signatureTransitions ((a :: ((xs ++ ys ++ zs) ++ [b])).map
      (fun v => full v / 2 ^ r)) = 0 := by
  apply zeroPrefixQuotient_transitions_eq_zero full _ r
  intro v hv
  apply hbound v
  simp only [List.mem_cons, List.mem_append] at hv ⊢
  tauto

#print axioms head_add_signatureTransitions_le
#print axioms signatureTransitions_sorted_lt
#print axioms signatureTransitions_move_sorted_endpoints_le
#print axioms fullSignatureOrder_perm
#print axioms fullSignatureOrder_pairwise
#print axioms quotientSignatures_pairwise
#print axioms quotientSignatures_transitions_le
#print axioms fullSignatureOrder_all_quotient_bounds
#print axioms quotientSignatures_move_endpoints_le
#print axioms binaryPrefixQuotient_lt
#print axioms fullSignatureOrder_binaryPrefix_bounds
#print axioms binaryPrefixQuotient_move_endpoints_le

#print axioms zeroPrefixQuotient_transitions_eq_zero
#print axioms fullSignatureOrder_zeroPrefix_eq_zero
#print axioms zeroPrefixQuotient_move_endpoints_eq_zero

end Erdos883Verified
