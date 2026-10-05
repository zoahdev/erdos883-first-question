import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements680_23 :
    ∀ b : Fin 227, 184 ≤ b.val → b.val < 192 → ∀ j : Fin 113, coreResourceRequirements 680 4 b.val (j.val + 1)
      (coreResources680 (coreSelector680 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements680_23
end Erdos883Verified
