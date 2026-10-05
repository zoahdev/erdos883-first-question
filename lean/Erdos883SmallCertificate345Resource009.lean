import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_9 :
    (List.ofFn coreChunks345_9).flatten =
      (coreData345.take (coreResources345 9).q).drop 70 := by
  decide +kernel

theorem coreCheck345_9 :
    ∀ c : Fin 1, (coreChunks345_9 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 9)) = true := by
  decide +kernel
#print axioms coreFlatten345_9
#print axioms coreCheck345_9
end Erdos883Verified
