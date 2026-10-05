import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements618_25 :
    ∀ b : Fin 206, 200 ≤ b.val → b.val < 206 → ∀ j : Fin 103, coreResourceRequirements 618 4 b.val (j.val + 1)
      (coreResources618 (coreSelector618 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements618_25
end Erdos883Verified
