import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_20 :
    (List.ofFn coreChunks345_20).flatten =
      (coreData345.take (coreResources345 20).q).drop 87 := by
  decide +kernel

theorem coreCheck345_20 :
    ∀ c : Fin 1, (coreChunks345_20 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 20)) = true := by
  decide +kernel
#print axioms coreFlatten345_20
#print axioms coreCheck345_20
end Erdos883Verified
