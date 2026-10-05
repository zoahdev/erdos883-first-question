import Erdos883AdaptiveCertificate126524Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics126524 : (coreProfileValues adaptiveRows126524).Nodup ∧ (coreProfileValues adaptiveRows126524).toFinset = oddUniverse 126524 := by
  rw [adaptiveRowsThroughEq126524]
  exact adaptiveRowsThrough_permutation (by decide : 126524 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
