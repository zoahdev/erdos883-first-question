import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements192_0 :
    ∀ b : Fin 64, ∀ j : Fin 32, coreResourceRequirements 192 4 b.val (j.val + 1)
      (coreResources192 (coreSelector192 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements192_0
end Erdos883Verified
