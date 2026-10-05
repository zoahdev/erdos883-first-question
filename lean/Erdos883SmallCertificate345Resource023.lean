import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_23 :
    (List.ofFn coreChunks345_23).flatten =
      (coreData345.take (coreResources345 23).q).drop 49 := by
  decide +kernel

theorem coreCheck345_23 :
    ∀ c : Fin 1, (coreChunks345_23 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 23)) = true := by
  decide +kernel
#print axioms coreFlatten345_23
#print axioms coreCheck345_23
end Erdos883Verified
