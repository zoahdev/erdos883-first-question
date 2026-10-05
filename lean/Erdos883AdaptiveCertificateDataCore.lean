import Erdos883AdaptiveCertificateCore
import Erdos883AdaptiveCertificateProfileCore
import Erdos883NumericDegreesCore
namespace Erdos883Verified

def coreDegreeEntries (scale W c d H : Nat) (shift : Bool)
    (rows : List AdaptiveProfileRow) : List (Nat × Nat) :=
  rows.zipIdx.map fun (r,i) => (i,
    if shift then coreNumericDegree scale W c d r.numerator r.value + H - i
    else coreNumericDegree scale W c d r.numerator r.value)
end Erdos883Verified
