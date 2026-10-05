import Erdos883AdaptiveCertificate17091Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics17091 : (coreProfileValues adaptiveRows17091).Nodup ∧ (coreProfileValues adaptiveRows17091).toFinset = oddUniverse 17091 := by
  rw [adaptiveRowsThroughEq17091]
  exact adaptiveRowsThrough_permutation (by decide : 17091 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
