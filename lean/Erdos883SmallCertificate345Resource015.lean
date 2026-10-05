import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_15 :
    (List.ofFn coreChunks345_15).flatten =
      (coreData345.take (coreResources345 15).q).drop 79 := by
  decide +kernel

theorem coreCheck345_15 :
    ∀ c : Fin 1, (coreChunks345_15 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 15)) = true := by
  decide +kernel
#print axioms coreFlatten345_15
#print axioms coreCheck345_15
end Erdos883Verified
