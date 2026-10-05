import Erdos883AdaptiveCertificate95058Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics95058 : (coreProfileValues adaptiveRows95058).Nodup ∧ (coreProfileValues adaptiveRows95058).toFinset = oddUniverse 95058 := by
  rw [adaptiveRowsThroughEq95058]
  exact adaptiveRowsThrough_permutation (by decide : 95058 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
