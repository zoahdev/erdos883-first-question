import Erdos883AdaptiveCertificate40310Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics40310 : (coreProfileValues adaptiveRows40310).Nodup ∧ (coreProfileValues adaptiveRows40310).toFinset = oddUniverse 40310 := by
  rw [adaptiveRowsThroughEq40310]
  exact adaptiveRowsThrough_permutation (by decide : 40310 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
