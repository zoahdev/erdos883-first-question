import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements999_32 :
    ∀ b : Fin 333, 256 ≤ b.val → b.val < 264 → ∀ j : Fin 166, coreResourceRequirements 999 4 b.val (j.val + 1)
      (coreResources999 (coreSelector999 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements999_32
end Erdos883Verified
