import Erdos883AdaptiveSpanCore
import Erdos883AdaptiveCertificateProfileCore
import Erdos883NumericDegreesCore

namespace Erdos883Verified

/-- One rational profile evaluation shared by a positive-length block of ranks. -/
structure AdaptiveNumericSpan where
  len : Nat
  numerator : Nat
  denominator : Nat
  evenDegree : Nat
  wholeDegree : Nat
  deriving DecidableEq

def adaptiveSpanFallback : AdaptiveProfileRow := ⟨1, [], 1⟩

/-- The take-length test and drop scan each covered row only a constant number of
 times; expensive numeric degree arithmetic is done once per span. -/
def coreNumericSpansCheck (L W c d : Nat) :
    List AdaptiveNumericSpan → List AdaptiveProfileRow → Bool
  | [], rows => rows.isEmpty
  | sp :: spans, rows =>
      decide (0 < sp.len ∧ (rows.take sp.len).length = sp.len ∧
        sp.numerator = (rows.headD adaptiveSpanFallback).numerator ∧
        sp.denominator = (rows.headD adaptiveSpanFallback).value ∧
        sp.evenDegree = coreNumericDegree (L / 2) W c d sp.numerator sp.denominator ∧
        sp.wholeDegree = coreNumericDegree L W c d sp.numerator sp.denominator) &&
      coreNumericSpansCheck L W c d spans (rows.drop sp.len)

def coreEvenSpans (H start : Nat) : List AdaptiveNumericSpan → List AdaptiveDegreeSpan
  | [] => []
  | sp :: spans =>
      ⟨start, start + sp.len - 1, sp.evenDegree + H - (start + sp.len - 1)⟩ ::
        coreEvenSpans H (start + sp.len) spans

def coreWholeSpans (start : Nat) : List AdaptiveNumericSpan → List AdaptiveDegreeSpan
  | [] => []
  | sp :: spans =>
      ⟨start, start + sp.len - 1, sp.wholeDegree⟩ ::
        coreWholeSpans (start + sp.len) spans

end Erdos883Verified
