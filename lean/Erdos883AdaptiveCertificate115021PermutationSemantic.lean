import Erdos883AdaptiveCertificate115021Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics115021 : (coreProfileValues adaptiveRows115021).Nodup ∧ (coreProfileValues adaptiveRows115021).toFinset = oddUniverse 115021 := by
  rw [adaptiveRowsThroughEq115021]
  exact adaptiveRowsThrough_permutation (by decide : 115021 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
