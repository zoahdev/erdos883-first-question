import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_25 :
    (List.ofFn coreChunks345_25).flatten =
      (coreData345.take (coreResources345 25).q).drop 55 := by
  decide +kernel

theorem coreCheck345_25 :
    ∀ c : Fin 1, (coreChunks345_25 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 25)) = true := by
  decide +kernel
#print axioms coreFlatten345_25
#print axioms coreCheck345_25
end Erdos883Verified
