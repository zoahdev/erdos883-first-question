import Erdos883AdaptiveCertificate78559Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics78559 : (coreProfileValues adaptiveRows78559).Nodup ∧ (coreProfileValues adaptiveRows78559).toFinset = oddUniverse 78559 := by
  rw [adaptiveRowsThroughEq78559]
  exact adaptiveRowsThrough_permutation (by decide : 78559 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
