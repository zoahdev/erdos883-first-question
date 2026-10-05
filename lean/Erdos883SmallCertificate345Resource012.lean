import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_12 :
    (List.ofFn coreChunks345_12).flatten =
      (coreData345.take (coreResources345 12).q).drop 74 := by
  decide +kernel

theorem coreCheck345_12 :
    ∀ c : Fin 1, (coreChunks345_12 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 12)) = true := by
  decide +kernel
#print axioms coreFlatten345_12
#print axioms coreCheck345_12
end Erdos883Verified
