import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_50 :
    (List.ofFn coreChunks345_50).flatten =
      (coreData345.take (coreResources345 50).q).drop 94 := by
  decide +kernel

theorem coreCheck345_50 :
    ∀ c : Fin 1, (coreChunks345_50 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 50)) = true := by
  decide +kernel
#print axioms coreFlatten345_50
#print axioms coreCheck345_50
end Erdos883Verified
