import Erdos883SmallCertificate313Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements313 :
    ∀ b : Fin 105, ∀ j : Fin 52, coreResourceRequirements 313 4 b.val (j.val + 1)
      (coreResources313 (coreSelector313 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements313
end Erdos883Verified
