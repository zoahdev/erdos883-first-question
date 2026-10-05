import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_17 :
    (List.ofFn coreChunks345_17).flatten =
      (coreData345.take (coreResources345 17).q).drop 81 := by
  decide +kernel

theorem coreCheck345_17 :
    ∀ c : Fin 1, (coreChunks345_17 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 17)) = true := by
  decide +kernel
#print axioms coreFlatten345_17
#print axioms coreCheck345_17
end Erdos883Verified
