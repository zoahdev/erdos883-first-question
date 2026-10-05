import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_3 :
    (List.ofFn coreChunks345_3).flatten =
      (coreData345.take (coreResources345 3).q).drop 42 := by
  decide +kernel

theorem coreCheck345_3 :
    ∀ c : Fin 1, (coreChunks345_3 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 3)) = true := by
  decide +kernel
#print axioms coreFlatten345_3
#print axioms coreCheck345_3
end Erdos883Verified
