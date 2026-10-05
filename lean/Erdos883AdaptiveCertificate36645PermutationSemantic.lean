import Erdos883AdaptiveCertificate36645Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics36645 : (coreProfileValues adaptiveRows36645).Nodup ∧ (coreProfileValues adaptiveRows36645).toFinset = oddUniverse 36645 := by
  rw [adaptiveRowsThroughEq36645]
  exact adaptiveRowsThrough_permutation (by decide : 36645 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
