import Erdos883AdaptiveCertificate30284Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics30284 : (coreProfileValues adaptiveRows30284).Nodup ∧ (coreProfileValues adaptiveRows30284).toFinset = oddUniverse 30284 := by
  rw [adaptiveRowsThroughEq30284]
  exact adaptiveRowsThrough_permutation (by decide : 30284 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
