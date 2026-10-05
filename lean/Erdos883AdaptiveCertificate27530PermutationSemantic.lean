import Erdos883AdaptiveCertificate27530Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics27530 : (coreProfileValues adaptiveRows27530).Nodup ∧ (coreProfileValues adaptiveRows27530).toFinset = oddUniverse 27530 := by
  rw [adaptiveRowsThroughEq27530]
  exact adaptiveRowsThrough_permutation (by decide : 27530 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
