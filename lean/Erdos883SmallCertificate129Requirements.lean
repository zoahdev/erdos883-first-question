import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements129_0 :
    ∀ b : Fin 43, ∀ j : Fin 21, coreResourceRequirements 129 4 b.val (j.val + 1)
      (coreResources129 (coreSelector129 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements129_0
end Erdos883Verified
