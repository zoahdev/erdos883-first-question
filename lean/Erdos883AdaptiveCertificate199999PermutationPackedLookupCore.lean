import Erdos883AdaptiveCertificate199999PermutationLookupCore

namespace Erdos883Verified

theorem adaptiveUnpack_getElem?_eq (count packed i : Nat) :
    (adaptiveUnpack count packed)[i]? =
      if i < count then some ((packed / 1048576^i) % 1048576) else none := by
  induction count generalizing packed i with
  | zero => simp [adaptiveUnpack]
  | succ count ih =>
      cases i with
      | zero => simp [adaptiveUnpack]
      | succ i =>
          simp only [adaptiveUnpack, List.getElem?_cons_succ]
          rw [ih]
          simp only [Nat.succ_lt_succ_iff, Nat.pow_succ, Nat.div_div_eq_div_mul]
          rw [Nat.mul_comm (1048576^i) 1048576]


inductive AdaptivePackedPermutationTree where
  | leaf (count packed : Nat)
  | node (split : Nat) (left right : AdaptivePackedPermutationTree)

def AdaptivePackedPermutationTree.chunks : AdaptivePackedPermutationTree → List (List Nat)
  | .leaf count packed => [adaptiveUnpack count packed]
  | .node _ left right => left.chunks ++ right.chunks

def AdaptivePackedPermutationTree.lookup : AdaptivePackedPermutationTree → Nat → Option Nat
  | .leaf count packed, i => if i < count then some ((packed / 1048576^i) % 1048576) else none
  | .node split left right, i =>
    if i < split then left.lookup i else right.lookup (i-split)

theorem AdaptivePackedPermutationTree.lookup_mem {t : AdaptivePackedPermutationTree} {i v : Nat}
    (h : t.lookup i = some v) : v ∈ t.chunks.flatten := by
  induction t generalizing i with
  | leaf count packed =>
      have hget : (adaptiveUnpack count packed)[i]? = some v := by
        rw [adaptiveUnpack_getElem?_eq]
        exact h
      simpa only [chunks, List.flatten_cons, List.flatten_nil, List.append_nil] using
        List.mem_of_getElem? hget
  | node split left right hl hr =>
      simp only [lookup] at h
      simp only [chunks, List.flatten_append, List.mem_append]
      split at h
      · exact Or.inl (hl h)
      · exact Or.inr (hr h)

def adaptivePackedPermutationInverseCheck (tree : AdaptivePackedPermutationTree) (start : Nat)
    (ranks : List Nat) : Bool :=
  match ranks with
  | [] => true
  | rank :: ranks => (tree.lookup rank == some (2*start+1)) &&
      adaptivePackedPermutationInverseCheck tree (start+1) ranks

theorem adaptivePackedPermutationInverseCheck_mem {tree : AdaptivePackedPermutationTree}
    {start : Nat} {ranks : List Nat}
    (h : adaptivePackedPermutationInverseCheck tree start ranks = true) :
    ∀ i < ranks.length, 2*(start+i)+1 ∈ tree.chunks.flatten := by
  induction ranks generalizing start with
  | nil => simp
  | cons rank ranks ih =>
      simp only [adaptivePackedPermutationInverseCheck, Bool.and_eq_true, beq_iff_eq] at h
      intro i hi
      cases i with
      | zero => simpa only [Nat.add_zero] using AdaptivePackedPermutationTree.lookup_mem h.1
      | succ i =>
          have hi' : i < ranks.length := by simpa using hi
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ih h.2 i hi'

theorem adaptivePackedPermutationCover_join {tree : AdaptivePackedPermutationTree} {lo mid hi : Nat}
    (hl : ∀ i, lo ≤ i → i < mid → 2*i+1 ∈ tree.chunks.flatten)
    (hr : ∀ i, mid ≤ i → i < hi → 2*i+1 ∈ tree.chunks.flatten) :
    ∀ i, lo ≤ i → i < hi → 2*i+1 ∈ tree.chunks.flatten := by
  intro i hlo hhi
  by_cases hmid : i < mid
  · exact hl i hlo hmid
  · exact hr i (by omega) hhi

theorem adaptivePackedPermutationInverseCheck_cover {tree : AdaptivePackedPermutationTree}
    {start count : Nat} {ranks : List Nat}
    (hlen : ranks.length = count)
    (h : adaptivePackedPermutationInverseCheck tree start ranks = true) :
    ∀ i, start ≤ i → i < start+count → 2*i+1 ∈ tree.chunks.flatten := by
  intro i hlo hhi
  have hk : i-start < ranks.length := by omega
  have hm := adaptivePackedPermutationInverseCheck_mem h (i-start) hk
  simpa only [Nat.add_sub_of_le hlo] using hm


end Erdos883Verified
