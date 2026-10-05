import Erdos883AdaptiveSpanCompactCore
namespace Erdos883Verified

/-- Blockwise checker retaining the absolute rank at each block boundary. -/
def adaptiveSpanZipIdxChunksCheck {α : Type} (p : α × Nat → Bool) :
    Nat → List (List α) → Bool
  | _, [] => true
  | start, xs :: xss => (xs.zipIdx start).all p &&
      adaptiveSpanZipIdxChunksCheck p (start + xs.length) xss

/-- Bounded independent witness checks imply the full flattened check. -/
theorem adaptiveSpanZipIdxChunksCheck_sound {α : Type} (p : α × Nat → Bool)
    (start : Nat) (chunks : List (List α))
    (h : adaptiveSpanZipIdxChunksCheck p start chunks = true) :
    (chunks.flatten.zipIdx start).all p = true := by
  induction chunks generalizing start with
  | nil => rfl
  | cons xs xss ih =>
      simp only [adaptiveSpanZipIdxChunksCheck, Bool.and_eq_true] at h
      rw [List.flatten_cons, List.zipIdx_append, List.all_append,
        h.1, ih _ h.2]
      rfl

#print axioms adaptiveSpanZipIdxChunksCheck_sound
end Erdos883Verified
