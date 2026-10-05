import Erdos883AdaptiveCertificate185246Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics185246 : (coreProfileValues adaptiveRows185246).Nodup ∧ (coreProfileValues adaptiveRows185246).toFinset = oddUniverse 185246 := by
  rw [adaptiveRowsThroughEq185246]
  exact adaptiveRowsThrough_permutation (by decide : 185246 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
