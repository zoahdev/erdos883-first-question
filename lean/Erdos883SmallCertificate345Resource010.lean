import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_10 :
    (List.ofFn coreChunks345_10).flatten =
      (coreData345.take (coreResources345 10).q).drop 72 := by
  decide +kernel

theorem coreCheck345_10 :
    ∀ c : Fin 1, (coreChunks345_10 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 10)) = true := by
  decide +kernel
#print axioms coreFlatten345_10
#print axioms coreCheck345_10
end Erdos883Verified
