import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements419_6 :
    ∀ b : Fin 140, 48 ≤ b.val → b.val < 56 → ∀ j : Fin 69, coreResourceRequirements 419 4 b.val (j.val + 1)
      (coreResources419 (coreSelector419 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements419_6
end Erdos883Verified
