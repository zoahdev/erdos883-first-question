import Erdos883AdaptiveCertificate86416Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics86416 : (coreProfileValues adaptiveRows86416).Nodup ∧ (coreProfileValues adaptiveRows86416).toFinset = oddUniverse 86416 := by
  rw [adaptiveRowsThroughEq86416]
  exact adaptiveRowsThrough_permutation (by decide : 86416 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
