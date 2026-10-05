import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements561_19 :
    ∀ b : Fin 187, 152 ≤ b.val → b.val < 160 → ∀ j : Fin 93, coreResourceRequirements 561 4 b.val (j.val + 1)
      (coreResources561 (coreSelector561 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements561_19
end Erdos883Verified
