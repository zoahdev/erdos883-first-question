import Erdos883AdaptiveCertificate168405Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics168405 : (coreProfileValues adaptiveRows168405).Nodup ∧ (coreProfileValues adaptiveRows168405).toFinset = oddUniverse 168405 := by
  rw [adaptiveRowsThroughEq168405]
  exact adaptiveRowsThrough_permutation (by decide : 168405 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
