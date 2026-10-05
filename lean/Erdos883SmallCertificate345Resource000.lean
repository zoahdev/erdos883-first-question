import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_0 :
    (List.ofFn coreChunks345_0).flatten =
      (coreData345.take (coreResources345 0).q).drop 0 := by
  decide +kernel

theorem coreCheck345_0 :
    ∀ c : Fin 2, (coreChunks345_0 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 0)) = true := by
  decide +kernel
#print axioms coreFlatten345_0
#print axioms coreCheck345_0
end Erdos883Verified
