import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements749_10 :
    ∀ b : Fin 250, 80 ≤ b.val → b.val < 88 → ∀ j : Fin 124, coreResourceRequirements 749 4 b.val (j.val + 1)
      (coreResources749 (coreSelector749 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements749_10
end Erdos883Verified
