import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements825_11 :
    ∀ b : Fin 275, 88 ≤ b.val → b.val < 96 → ∀ j : Fin 137, coreResourceRequirements 825 4 b.val (j.val + 1)
      (coreResources825 (coreSelector825 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements825_11
end Erdos883Verified
