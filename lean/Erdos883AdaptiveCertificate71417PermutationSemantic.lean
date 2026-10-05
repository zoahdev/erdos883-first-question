import Erdos883AdaptiveCertificate71417Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics71417 : (coreProfileValues adaptiveRows71417).Nodup ∧ (coreProfileValues adaptiveRows71417).toFinset = oddUniverse 71417 := by
  rw [adaptiveRowsThroughEq71417]
  exact adaptiveRowsThrough_permutation (by decide : 71417 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
