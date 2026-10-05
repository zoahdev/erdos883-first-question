import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements31_0 :
    ∀ b : Fin 11, ∀ j : Fin 5, coreResourceRequirements 31 4 b.val (j.val + 1)
      (coreResources31 (coreSelector31 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements31_0
end Erdos883Verified
