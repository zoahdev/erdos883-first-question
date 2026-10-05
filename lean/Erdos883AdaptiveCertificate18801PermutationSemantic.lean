import Erdos883AdaptiveCertificate18801Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics18801 : (coreProfileValues adaptiveRows18801).Nodup ∧ (coreProfileValues adaptiveRows18801).toFinset = oddUniverse 18801 := by
  rw [adaptiveRowsThroughEq18801]
  exact adaptiveRowsThrough_permutation (by decide : 18801 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
