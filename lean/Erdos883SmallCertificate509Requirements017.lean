import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements509_17 :
    ∀ b : Fin 170, 136 ≤ b.val → b.val < 144 → ∀ j : Fin 84, coreResourceRequirements 509 4 b.val (j.val + 1)
      (coreResources509 (coreSelector509 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements509_17
end Erdos883Verified
