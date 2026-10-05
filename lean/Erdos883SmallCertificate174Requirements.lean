import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements174_0 :
    ∀ b : Fin 58, ∀ j : Fin 29, coreResourceRequirements 174 4 b.val (j.val + 1)
      (coreResources174 (coreSelector174 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements174_0
end Erdos883Verified
