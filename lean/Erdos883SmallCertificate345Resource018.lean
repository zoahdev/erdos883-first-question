import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_18 :
    (List.ofFn coreChunks345_18).flatten =
      (coreData345.take (coreResources345 18).q).drop 84 := by
  decide +kernel

theorem coreCheck345_18 :
    ∀ c : Fin 1, (coreChunks345_18 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 18)) = true := by
  decide +kernel
#print axioms coreFlatten345_18
#print axioms coreCheck345_18
end Erdos883Verified
