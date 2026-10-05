import Erdos883AdaptiveCertificate104564Reuse
import Erdos883AdaptiveCertificate199999PermutationSemantic
namespace Erdos883Verified
theorem adaptivePermutationSemantics104564 : (coreProfileValues adaptiveRows104564).Nodup ∧ (coreProfileValues adaptiveRows104564).toFinset = oddUniverse 104564 := by
  rw [adaptiveRowsThroughEq104564]
  exact adaptiveRowsThrough_permutation (by decide : 104564 ≤ 199999) adaptivePermutationSemantics199999.1 adaptivePermutationSemantics199999.2
end Erdos883Verified
