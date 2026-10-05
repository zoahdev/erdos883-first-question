import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreRequirements92_0 :
    ∀ b : Fin 31, ∀ j : Fin 15, coreResourceRequirements 92 4 b.val (j.val + 1)
      (coreResources92 (coreSelector92 b j)) := by
  unfold coreResourceRequirements
  decide +kernel
#print axioms coreRequirements92_0
end Erdos883Verified
