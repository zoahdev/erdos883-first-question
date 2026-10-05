import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements561_1 :
    ∀ b : Fin 187, 8 ≤ b.val → b.val < 16 → ∀ j : Fin 93, coreResourceRequirements 561 4 b.val (j.val + 1)
      (coreResources561 (coreSelector561 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements561_1
end Erdos883Verified
