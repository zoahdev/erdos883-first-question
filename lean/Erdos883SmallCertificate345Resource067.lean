import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_67 :
    (List.ofFn coreChunks345_67).flatten =
      (coreData345.take (coreResources345 67).q).drop 0 := by
  decide +kernel

theorem coreCheck345_67 :
    ∀ c : Fin 7, (coreChunks345_67 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 67)) = true := by
  decide +kernel
#print axioms coreFlatten345_67
#print axioms coreCheck345_67
end Erdos883Verified
