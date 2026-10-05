import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements93_0 :
    ∀ b : Fin 31, ∀ j : Fin 15, coreResourceRequirements 93 4 b.val (j.val + 1)
      (coreResources93 (coreSelector93 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements93_0
end Erdos883Verified
