import Erdos883SmallCertificate380Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements380_0 :
    ∀ b : Fin 127, ∀ j : Fin 63, coreResourceRequirements 380 4 b.val (j.val + 1)
      (coreResources380 (coreSelector380 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements380_0
end Erdos883Verified
