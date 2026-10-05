import Erdos883AdaptiveCertificate20682Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics20682 : (coreProfileValues adaptiveRows20682).Nodup ∧ (coreProfileValues adaptiveRows20682).toFinset = oddUniverse 20682 := by
  rw [adaptiveRowsThroughEq20682]
  exact adaptiveRowsThrough_permutation (by decide : 20682 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
