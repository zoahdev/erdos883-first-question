import Erdos883SmallCertificate234Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements234 :
    ∀ b : Fin 78, ∀ j : Fin 39, coreResourceRequirements 234 4 b.val (j.val + 1)
      (coreResources234 (coreSelector234 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements234
end Erdos883Verified
