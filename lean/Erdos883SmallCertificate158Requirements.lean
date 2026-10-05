import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements158_0 :
    ∀ b : Fin 53, ∀ j : Fin 26, coreResourceRequirements 158 4 b.val (j.val + 1)
      (coreResources158 (coreSelector158 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements158_0
end Erdos883Verified
