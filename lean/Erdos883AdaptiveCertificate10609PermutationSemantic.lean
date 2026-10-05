import Erdos883AdaptiveCertificate10609Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics10609 : (coreProfileValues adaptiveRows10609).Nodup ∧ (coreProfileValues adaptiveRows10609).toFinset = oddUniverse 10609 := by
  rw [adaptiveRowsThroughEq10609]
  exact adaptiveRowsThrough_permutation (by decide : 10609 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
