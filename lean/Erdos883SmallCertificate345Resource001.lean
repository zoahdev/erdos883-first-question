import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_1 :
    (List.ofFn coreChunks345_1).flatten =
      (coreData345.take (coreResources345 1).q).drop 32 := by
  decide +kernel

theorem coreCheck345_1 :
    ∀ c : Fin 1, (coreChunks345_1 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 1)) = true := by
  decide +kernel
#print axioms coreFlatten345_1
#print axioms coreCheck345_1
end Erdos883Verified
