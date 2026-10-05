import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements83_0 :
    ∀ b : Fin 28, ∀ j : Fin 13, coreResourceRequirements 83 4 b.val (j.val + 1)
      (coreResources83 (coreSelector83 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements83_0
end Erdos883Verified
