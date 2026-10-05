import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements618_2 :
    ∀ b : Fin 206, 16 ≤ b.val → b.val < 24 → ∀ j : Fin 103, coreResourceRequirements 618 4 b.val (j.val + 1)
      (coreResources618 (coreSelector618 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements618_2
end Erdos883Verified
