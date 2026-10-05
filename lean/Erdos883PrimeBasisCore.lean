import Erdos883AdaptiveCertificateProfileCore
namespace Erdos883Verified
def smallPrimeTrialBasis : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443]
def coreBasisPrimeCheck (p : Nat) : Bool :=
  decide (2 ≤ p ∧ p ≤ 200000) &&
    smallPrimeTrialBasis.all (fun q => decide (p < q*q ∨ p % q ≠ 0))
def coreBasisProfileRowCheck (row : AdaptiveProfileRow) : Bool :=
  decide (0 < row.value) &&
    (decide (row.factors.prod = row.value) &&
      (row.factors.all coreBasisPrimeCheck &&
        decide (row.numerator = corePrimeSieveCount row.value (coreDedup row.factors))))
def coreBasisProfileMetadataCheck (rows : List AdaptiveProfileRow) : Bool :=
  rows.all coreBasisProfileRowCheck
end Erdos883Verified
