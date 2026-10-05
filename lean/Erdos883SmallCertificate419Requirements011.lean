import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements419_11 :
    ∀ b : Fin 140, 88 ≤ b.val → b.val < 96 → ∀ j : Fin 69, coreResourceRequirements 419 4 b.val (j.val + 1)
      (coreResources419 (coreSelector419 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements419_11
end Erdos883Verified
