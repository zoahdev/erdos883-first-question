import Erdos883AdaptiveCertificate15537Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics15537 : (coreProfileValues adaptiveRows15537).Nodup ∧ (coreProfileValues adaptiveRows15537).toFinset = oddUniverse 15537 := by
  rw [adaptiveRowsThroughEq15537]
  exact adaptiveRowsThrough_permutation (by decide : 15537 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
