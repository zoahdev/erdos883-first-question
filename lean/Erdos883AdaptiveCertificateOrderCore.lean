import Erdos883AdaptiveCertificateProfileCore
namespace Erdos883Verified

def coreProfileBoundaryCheck (xs ys : List AdaptiveProfileRow) : Bool :=
  match xs.getLast?, ys.head? with
  | some a, some b => decide (a.numerator * b.value ≤ b.numerator * a.value)
  | _, _ => true

def coreProfileChunkBoundaryCheck : List (List AdaptiveProfileRow) → Bool
  | [] => true
  | [_] => true
  | a :: b :: chunks => coreProfileBoundaryCheck a b && coreProfileChunkBoundaryCheck (b::chunks)
end Erdos883Verified
