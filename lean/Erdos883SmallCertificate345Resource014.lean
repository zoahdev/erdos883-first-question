import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_14 :
    (List.ofFn coreChunks345_14).flatten =
      (coreData345.take (coreResources345 14).q).drop 76 := by
  decide +kernel

theorem coreCheck345_14 :
    ∀ c : Fin 1, (coreChunks345_14 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 14)) = true := by
  decide +kernel
#print axioms coreFlatten345_14
#print axioms coreCheck345_14
end Erdos883Verified
