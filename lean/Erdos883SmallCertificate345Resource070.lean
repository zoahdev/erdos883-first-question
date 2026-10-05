import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_70 :
    (List.ofFn coreChunks345_70).flatten =
      (coreData345.take (coreResources345 70).q).drop 0 := by
  decide +kernel

theorem coreCheck345_70 :
    ∀ c : Fin 7, (coreChunks345_70 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 70)) = true := by
  decide +kernel
#print axioms coreFlatten345_70
#print axioms coreCheck345_70
end Erdos883Verified
