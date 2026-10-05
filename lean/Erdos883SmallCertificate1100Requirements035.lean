import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements1100_35 :
    ∀ b : Fin 367, 280 ≤ b.val → b.val < 288 → ∀ j : Fin 183, coreResourceRequirements 1100 4 b.val (j.val + 1)
      (coreResources1100 (coreSelector1100 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements1100_35
end Erdos883Verified
