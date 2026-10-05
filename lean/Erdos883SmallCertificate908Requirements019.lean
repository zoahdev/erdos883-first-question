import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements908_19 :
    ∀ b : Fin 303, 152 ≤ b.val → b.val < 160 → ∀ j : Fin 151, coreResourceRequirements 908 4 b.val (j.val + 1)
      (coreResources908 (coreSelector908 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements908_19
end Erdos883Verified
