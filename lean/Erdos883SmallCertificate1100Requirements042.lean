import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements1100_42 :
    ∀ b : Fin 367, 336 ≤ b.val → b.val < 344 → ∀ j : Fin 183, coreResourceRequirements 1100 4 b.val (j.val + 1)
      (coreResources1100 (coreSelector1100 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements1100_42
end Erdos883Verified
