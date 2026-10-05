import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_28 :
    (List.ofFn coreChunks345_28).flatten =
      (coreData345.take (coreResources345 28).q).drop 59 := by
  decide +kernel

theorem coreCheck345_28 :
    ∀ c : Fin 1, (coreChunks345_28 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 28)) = true := by
  decide +kernel
#print axioms coreFlatten345_28
#print axioms coreCheck345_28
end Erdos883Verified
