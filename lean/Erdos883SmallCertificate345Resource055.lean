import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_55 :
    (List.ofFn coreChunks345_55).flatten =
      (coreData345.take (coreResources345 55).q).drop 106 := by
  decide +kernel

theorem coreCheck345_55 :
    ∀ c : Fin 1, (coreChunks345_55 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 55)) = true := by
  decide +kernel
#print axioms coreFlatten345_55
#print axioms coreCheck345_55
end Erdos883Verified
