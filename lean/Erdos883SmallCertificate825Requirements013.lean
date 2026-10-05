import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements825_13 :
    ∀ b : Fin 275, 104 ≤ b.val → b.val < 112 → ∀ j : Fin 137, coreResourceRequirements 825 4 b.val (j.val + 1)
      (coreResources825 (coreSelector825 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements825_13
end Erdos883Verified
