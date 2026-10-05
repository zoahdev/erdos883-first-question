import Erdos883AdaptiveSpanRowsCore
import Erdos883AdaptiveCertificateCompactCore
namespace Erdos883Verified

def adaptiveDecodeNumericSpans : Nat → List Nat → List AdaptiveNumericSpan
  | 0, _ => []
  | k+1, len :: a :: b :: e :: r :: rest => ⟨len,a,b,e,r⟩ :: adaptiveDecodeNumericSpans k rest
  | _+1, _ => []

def adaptivePackedNumericSpans (count packed : Nat) : List AdaptiveNumericSpan :=
  adaptiveDecodeNumericSpans count (adaptiveUnpack (5*count) packed)

def adaptiveBuildSpanTree : Nat → List AdaptiveDegreeSpan → AdaptiveSpanTree
  | 0, xs => let s := xs.headD ⟨0,0,0⟩; .leaf s.lo s.hi s.minimum
  | fuel+1, xs =>
    if xs.length ≤ 1 then let s := xs.headD ⟨0,0,0⟩; .leaf s.lo s.hi s.minimum
    else
      let k := xs.length/2
      let l := adaptiveBuildSpanTree fuel (xs.take k)
      let r := adaptiveBuildSpanTree fuel (xs.drop k)
      .node l.low r.high (min l.minimum r.minimum) l r

def adaptiveSpanTreeOfSpans (spans : List AdaptiveDegreeSpan) :=
  adaptiveBuildSpanTree (Nat.log2 spans.length + 1) spans

/-- A linear fuel budget has a simple structural completeness proof. -/
def adaptiveSpanTreeOfSpansLinearFuel (spans : List AdaptiveDegreeSpan) :=
  adaptiveBuildSpanTree spans.length spans

end Erdos883Verified
