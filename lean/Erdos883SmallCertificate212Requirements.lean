import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements212_0 :
    ∀ b : Fin 71, ∀ j : Fin 35, coreResourceRequirements 212 4 b.val (j.val + 1)
      (coreResources212 (coreSelector212 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements212_0
end Erdos883Verified
