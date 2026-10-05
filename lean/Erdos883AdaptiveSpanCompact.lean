import Erdos883AdaptiveSpanCompactCore
import Mathlib.Data.List.TakeDrop

namespace Erdos883Verified

/-- Every nonempty leaf list is preserved when the builder has sufficient fuel. -/
theorem adaptiveBuildSpanTree_spans (fuel : Nat) (xs : List AdaptiveDegreeSpan)
    (hpos : 0 < xs.length) (hfuel : xs.length ≤ fuel) :
    (adaptiveBuildSpanTree fuel xs).spans = xs := by
  induction fuel generalizing xs with
  | zero => omega
  | succ fuel ih =>
      by_cases hsmall : xs.length ≤ 1
      · cases xs with
        | nil => simp at hpos
        | cons x xs =>
            have hx : xs = [] := by simpa using hsmall
            subst xs
            simp [adaptiveBuildSpanTree, AdaptiveSpanTree.spans]
      · have hlength : 1 < xs.length := by omega
        have hhalf : 0 < xs.length / 2 := by omega
        have hhalfLt : xs.length / 2 < xs.length := by omega
        have htpos : 0 < (xs.take (xs.length / 2)).length := by
          simp only [List.length_take]
          omega
        have hdpos : 0 < (xs.drop (xs.length / 2)).length := by
          simp only [List.length_drop]
          omega
        have htfuel : (xs.take (xs.length / 2)).length ≤ fuel := by
          simp only [List.length_take]
          omega
        have hdfuel : (xs.drop (xs.length / 2)).length ≤ fuel := by
          simp only [List.length_drop]
          omega
        simp only [adaptiveBuildSpanTree, hsmall, ↓reduceIte, AdaptiveSpanTree.spans]
        rw [ih _ htpos htfuel, ih _ hdpos hdfuel, List.take_append_drop]

theorem coreEvenSpans_length (H start : Nat) (xs : List AdaptiveNumericSpan) :
    (coreEvenSpans H start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [coreEvenSpans, List.length_cons, ih]

theorem coreWholeSpans_length (start : Nat) (xs : List AdaptiveNumericSpan) :
    (coreWholeSpans start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [coreWholeSpans, List.length_cons, ih]

/-- Linear-fuel construction preserves the input spans, without normalization. -/
theorem adaptiveSpanTreeOfSpansLinearFuel_spans (xs : List AdaptiveDegreeSpan)
    (hpos : 0 < xs.length) : (adaptiveSpanTreeOfSpansLinearFuel xs).spans = xs :=
  adaptiveBuildSpanTree_spans xs.length xs hpos (Nat.le_refl _)

#print axioms adaptiveBuildSpanTree_spans
#print axioms adaptiveSpanTreeOfSpansLinearFuel_spans
end Erdos883Verified
