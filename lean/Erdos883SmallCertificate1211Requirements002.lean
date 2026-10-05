import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements1211_2 :
    ∀ b : Fin 404, 16 ≤ b.val → b.val < 24 → ∀ j : Fin 201, coreResourceRequirements 1211 4 b.val (j.val + 1)
      (coreResources1211 (coreSelector1211 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements1211_2
end Erdos883Verified
