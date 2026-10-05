import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_16 :
    (List.ofFn coreChunks345_16).flatten =
      (coreData345.take (coreResources345 16).q).drop 80 := by
  decide +kernel

theorem coreCheck345_16 :
    ∀ c : Fin 1, (coreChunks345_16 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 16)) = true := by
  decide +kernel
#print axioms coreFlatten345_16
#print axioms coreCheck345_16
end Erdos883Verified
