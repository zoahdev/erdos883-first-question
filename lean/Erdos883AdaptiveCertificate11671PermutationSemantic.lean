import Erdos883AdaptiveCertificate11671Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics11671 : (coreProfileValues adaptiveRows11671).Nodup ∧ (coreProfileValues adaptiveRows11671).toFinset = oddUniverse 11671 := by
  rw [adaptiveRowsThroughEq11671]
  exact adaptiveRowsThrough_permutation (by decide : 11671 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
