import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements103_0 :
    ∀ b : Fin 35, ∀ j : Fin 17, coreResourceRequirements 103 4 b.val (j.val + 1)
      (coreResources103 (coreSelector103 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements103_0
end Erdos883Verified
