import Erdos883AdaptiveCertificate153095Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics153095 : (coreProfileValues adaptiveRows153095).Nodup ∧ (coreProfileValues adaptiveRows153095).toFinset = oddUniverse 153095 := by
  rw [adaptiveRowsThroughEq153095]
  exact adaptiveRowsThrough_permutation (by decide : 153095 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
