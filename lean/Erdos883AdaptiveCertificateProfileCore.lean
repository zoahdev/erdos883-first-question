import Erdos883SmallCertificateCore

namespace Erdos883Verified

/-- A positive integer together with a checked factorization and totient numerator. -/
structure AdaptiveProfileRow where
  value : Nat
  factors : List Nat
  numerator : Nat
  deriving DecidableEq

def coreProfileValues (rows : List AdaptiveProfileRow) : List Nat :=
  rows.map (·.value)

def coreProfileRowCheck (row : AdaptiveProfileRow) : Bool :=
  decide (0 < row.value) &&
    (decide (row.factors.prod = row.value) &&
      (row.factors.all corePrimeCheck &&
        decide (row.numerator = corePrimeSieveCount row.value (coreDedup row.factors))))

def coreProfileMetadataCheck (rows : List AdaptiveProfileRow) : Bool :=
  rows.all coreProfileRowCheck

/-- An adjacent integer cross-product check certifies an increasing profile order. -/
def coreProfileOrderCheck : List AdaptiveProfileRow → Bool
  | [] => true
  | [_] => true
  | a :: b :: rows =>
      decide (a.numerator * b.value ≤ b.numerator * a.value) &&
        coreProfileOrderCheck (b :: rows)

end Erdos883Verified
