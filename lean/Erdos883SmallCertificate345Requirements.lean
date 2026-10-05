import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements345_0 :
    ∀ b : Fin 115, ∀ j : Fin 57, coreResourceRequirements 345 4 b.val (j.val + 1)
      (coreResources345 (coreSelector345 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements345_0
end Erdos883Verified
