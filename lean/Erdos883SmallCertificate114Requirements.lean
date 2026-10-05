import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements114_0 :
    ∀ b : Fin 38, ∀ j : Fin 19, coreResourceRequirements 114 4 b.val (j.val + 1)
      (coreResources114 (coreSelector114 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements114_0
end Erdos883Verified
