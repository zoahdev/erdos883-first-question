import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_58 :
    (List.ofFn coreChunks345_58).flatten =
      (coreData345.take (coreResources345 58).q).drop 115 := by
  decide +kernel

theorem coreCheck345_58 :
    ∀ c : Fin 1, (coreChunks345_58 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 58)) = true := by
  decide +kernel
#print axioms coreFlatten345_58
#print axioms coreCheck345_58
end Erdos883Verified
