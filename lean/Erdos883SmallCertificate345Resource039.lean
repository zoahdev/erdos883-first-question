import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_39 :
    (List.ofFn coreChunks345_39).flatten =
      (coreData345.take (coreResources345 39).q).drop 74 := by
  decide +kernel

theorem coreCheck345_39 :
    ∀ c : Fin 1, (coreChunks345_39 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 39)) = true := by
  decide +kernel
#print axioms coreFlatten345_39
#print axioms coreCheck345_39
end Erdos883Verified
