import Erdos883AdaptiveCertificatePermutation
import Erdos883AdaptiveCertificateCompactCore

namespace Erdos883Verified

inductive AdaptivePermutationTree where
  | leaf (values : List Nat)
  | node (split : Nat) (left right : AdaptivePermutationTree)

def AdaptivePermutationTree.chunks : AdaptivePermutationTree → List (List Nat)
  | .leaf values => [values]
  | .node _ left right => left.chunks ++ right.chunks

def AdaptivePermutationTree.lookup : AdaptivePermutationTree → Nat → Option Nat
  | .leaf values, i => values[i]?
  | .node split left right, i =>
    if i < split then left.lookup i else right.lookup (i-split)

theorem AdaptivePermutationTree.lookup_mem {t : AdaptivePermutationTree} {i v : Nat}
    (h : t.lookup i = some v) : v ∈ t.chunks.flatten := by
  induction t generalizing i with
  | leaf values =>
      simp only [lookup] at h
      simpa only [chunks, List.flatten_cons, List.flatten_nil, List.append_nil] using
        List.mem_of_getElem? h
  | node split left right hl hr =>
      simp only [lookup] at h
      simp only [chunks, List.flatten_append, List.mem_append]
      split at h
      · exact Or.inl (hl h)
      · exact Or.inr (hr h)

def adaptivePermutationInverseCheck (tree : AdaptivePermutationTree) (start : Nat)
    (ranks : List Nat) : Bool :=
  match ranks with
  | [] => true
  | rank :: ranks => (tree.lookup rank == some (2*start+1)) &&
      adaptivePermutationInverseCheck tree (start+1) ranks

theorem adaptivePermutationInverseCheck_mem {tree : AdaptivePermutationTree}
    {start : Nat} {ranks : List Nat}
    (h : adaptivePermutationInverseCheck tree start ranks = true) :
    ∀ i < ranks.length, 2*(start+i)+1 ∈ tree.chunks.flatten := by
  induction ranks generalizing start with
  | nil => simp
  | cons rank ranks ih =>
      simp only [adaptivePermutationInverseCheck, Bool.and_eq_true, beq_iff_eq] at h
      intro i hi
      cases i with
      | zero => simpa only [Nat.add_zero] using AdaptivePermutationTree.lookup_mem h.1
      | succ i =>
          have hi' : i < ranks.length := by simpa using hi
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ih h.2 i hi'

theorem adaptivePermutationCover_join {tree : AdaptivePermutationTree} {lo mid hi : Nat}
    (hl : ∀ i, lo ≤ i → i < mid → 2*i+1 ∈ tree.chunks.flatten)
    (hr : ∀ i, mid ≤ i → i < hi → 2*i+1 ∈ tree.chunks.flatten) :
    ∀ i, lo ≤ i → i < hi → 2*i+1 ∈ tree.chunks.flatten := by
  intro i hlo hhi
  by_cases hmid : i < mid
  · exact hl i hlo hmid
  · exact hr i (by omega) hhi

theorem adaptivePermutationInverseCheck_cover {tree : AdaptivePermutationTree}
    {start count : Nat} {ranks : List Nat}
    (hlen : ranks.length = count)
    (h : adaptivePermutationInverseCheck tree start ranks = true) :
    ∀ i, start ≤ i → i < start+count → 2*i+1 ∈ tree.chunks.flatten := by
  intro i hlo hhi
  have hk : i-start < ranks.length := by omega
  have hm := adaptivePermutationInverseCheck_mem h (i-start) hk
  simpa only [Nat.add_sub_of_le hlo] using hm

end Erdos883Verified
