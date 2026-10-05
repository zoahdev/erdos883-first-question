import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_5 :
    (List.ofFn coreChunks345_5).flatten =
      (coreData345.take (coreResources345 5).q).drop 46 := by
  decide +kernel

theorem coreCheck345_5 :
    ∀ c : Fin 2, (coreChunks345_5 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 5)) = true := by
  decide +kernel
#print axioms coreFlatten345_5
#print axioms coreCheck345_5
end Erdos883Verified
