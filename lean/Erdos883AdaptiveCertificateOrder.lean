import Erdos883AdaptiveCertificateProfiles
import Erdos883AdaptiveCertificateOrderCore
namespace Erdos883Verified

theorem coreProfileOrderCheck_append {xs ys : List AdaptiveProfileRow}
    (hx : coreProfileOrderCheck xs = true) (hy : coreProfileOrderCheck ys = true)
    (hc : coreProfileBoundaryCheck xs ys = true) :
    coreProfileOrderCheck (xs ++ ys) = true := by
  induction xs with
  | nil => simpa using hy
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        simpa only [List.singleton_append, coreProfileOrderCheck, Bool.and_eq_true] using
          And.intro (by simpa [coreProfileBoundaryCheck] using hc) hy
    | cons b xs =>
      have hx' : decide (a.numerator * b.value ≤ b.numerator * a.value) = true ∧
          coreProfileOrderCheck (b::xs) = true := by simpa [coreProfileOrderCheck] using hx
      have hc' : coreProfileBoundaryCheck (b::xs) ys = true := by
        simpa [coreProfileBoundaryCheck] using hc
      have ht := ih hx'.2 hc'
      simpa only [List.cons_append, coreProfileOrderCheck, hx'.1, Bool.true_and] using ht
theorem coreProfileOrderCheck_flatten_chunks (chunks : List (List AdaptiveProfileRow))
    (hne : chunks.all (fun xs => !xs.isEmpty) = true)
    (hc : chunks.all coreProfileOrderCheck = true)
    (hb : coreProfileChunkBoundaryCheck chunks = true) :
    coreProfileOrderCheck chunks.flatten = true := by
  induction chunks with
  | nil => rfl
  | cons x chunks ih =>
    cases chunks with
    | nil => simpa using hc
    | cons y chunks =>
      have hne' : (y::chunks).all (fun xs => !xs.isEmpty) = true := by
        apply List.all_eq_true.mpr
        intro z hz
        exact List.all_eq_true.mp hne z (List.mem_cons_of_mem _ hz)
      have hc' : (y::chunks).all coreProfileOrderCheck = true := by
        apply List.all_eq_true.mpr
        intro z hz
        exact List.all_eq_true.mp hc z (List.mem_cons_of_mem _ hz)
      have hyne : y ≠ [] := by
        have hy := List.all_eq_true.mp hne' y (by simp)
        simpa using hy
      have hx := List.all_eq_true.mp hc x (by simp)
      have hb' : coreProfileBoundaryCheck x y = true ∧
          coreProfileChunkBoundaryCheck (y::chunks) = true := by
        simpa only [coreProfileChunkBoundaryCheck, Bool.and_eq_true] using hb
      have ht := ih hne' hc' hb'.2
      apply coreProfileOrderCheck_append hx ht
      simpa only [coreProfileBoundaryCheck, List.flatten_cons, List.head?_append,
        List.head?_eq_some_head hyne, Option.some_or] using hb'.1

#print axioms coreProfileOrderCheck_flatten_chunks
end Erdos883Verified
