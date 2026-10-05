import Erdos883AdaptiveCertificate53655Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics53655 : (coreProfileValues adaptiveRows53655).Nodup ∧ (coreProfileValues adaptiveRows53655).toFinset = oddUniverse 53655 := by
  rw [adaptiveRowsThroughEq53655]
  exact adaptiveRowsThrough_permutation (by decide : 53655 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
