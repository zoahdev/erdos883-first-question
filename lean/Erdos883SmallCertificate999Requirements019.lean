import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements999_19 :
    ∀ b : Fin 333, 152 ≤ b.val → b.val < 160 → ∀ j : Fin 166, coreResourceRequirements 999 4 b.val (j.val + 1)
      (coreResources999 (coreSelector999 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements999_19
end Erdos883Verified
