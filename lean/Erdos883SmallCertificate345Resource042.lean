import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_42 :
    (List.ofFn coreChunks345_42).flatten =
      (coreData345.take (coreResources345 42).q).drop 81 := by
  decide +kernel

theorem coreCheck345_42 :
    ∀ c : Fin 1, (coreChunks345_42 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 42)) = true := by
  decide +kernel
#print axioms coreFlatten345_42
#print axioms coreCheck345_42
end Erdos883Verified
