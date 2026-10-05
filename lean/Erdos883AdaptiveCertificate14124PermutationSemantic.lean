import Erdos883AdaptiveCertificate14124Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics14124 : (coreProfileValues adaptiveRows14124).Nodup ∧ (coreProfileValues adaptiveRows14124).toFinset = oddUniverse 14124 := by
  rw [adaptiveRowsThroughEq14124]
  exact adaptiveRowsThrough_permutation (by decide : 14124 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
