import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements284 :
    ∀ b : Fin 95, ∀ j : Fin 47, coreResourceRequirements 284 4 b.val (j.val + 1)
      (coreResources284 (coreSelector284 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements284
end Erdos883Verified
