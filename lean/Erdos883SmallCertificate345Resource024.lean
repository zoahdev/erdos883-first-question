import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_24 :
    (List.ofFn coreChunks345_24).flatten =
      (coreData345.take (coreResources345 24).q).drop 54 := by
  decide +kernel

theorem coreCheck345_24 :
    ∀ c : Fin 1, (coreChunks345_24 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 24)) = true := by
  decide +kernel
#print axioms coreFlatten345_24
#print axioms coreCheck345_24
end Erdos883Verified
