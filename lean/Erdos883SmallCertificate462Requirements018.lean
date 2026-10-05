import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements462_18 :
    ∀ b : Fin 154, 144 ≤ b.val → b.val < 152 → ∀ j : Fin 77, coreResourceRequirements 462 4 b.val (j.val + 1)
      (coreResources462 (coreSelector462 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements462_18
end Erdos883Verified
