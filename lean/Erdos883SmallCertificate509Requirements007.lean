import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements509_7 :
    ∀ b : Fin 170, 56 ≤ b.val → b.val < 64 → ∀ j : Fin 84, coreResourceRequirements 509 4 b.val (j.val + 1)
      (coreResources509 (coreSelector509 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements509_7
end Erdos883Verified
