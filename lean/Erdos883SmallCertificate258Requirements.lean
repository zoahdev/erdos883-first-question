import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements258 :
    ∀ b : Fin 86, ∀ j : Fin 43, coreResourceRequirements 258 4 b.val (j.val + 1)
      (coreResources258 (coreSelector258 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements258
end Erdos883Verified
