import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements419_1 :
    ∀ b : Fin 140, 8 ≤ b.val → b.val < 16 → ∀ j : Fin 69, coreResourceRequirements 419 4 b.val (j.val + 1)
      (coreResources419 (coreSelector419 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements419_1
end Erdos883Verified
