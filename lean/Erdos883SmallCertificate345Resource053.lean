import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_53 :
    (List.ofFn coreChunks345_53).flatten =
      (coreData345.take (coreResources345 53).q).drop 102 := by
  decide +kernel

theorem coreCheck345_53 :
    ∀ c : Fin 1, (coreChunks345_53 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 53)) = true := by
  decide +kernel
#print axioms coreFlatten345_53
#print axioms coreCheck345_53
end Erdos883Verified
