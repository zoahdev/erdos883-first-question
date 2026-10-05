import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_48 :
    (List.ofFn coreChunks345_48).flatten =
      (coreData345.take (coreResources345 48).q).drop 90 := by
  decide +kernel

theorem coreCheck345_48 :
    ∀ c : Fin 1, (coreChunks345_48 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 48)) = true := by
  decide +kernel
#print axioms coreFlatten345_48
#print axioms coreCheck345_48
end Erdos883Verified
