import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements35_0 :
    ∀ b : Fin 12, ∀ j : Fin 5, coreResourceRequirements 35 4 b.val (j.val + 1)
      (coreResources35 (coreSelector35 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements35_0
end Erdos883Verified
