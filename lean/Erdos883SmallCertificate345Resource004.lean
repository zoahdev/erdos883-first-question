import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_4 :
    (List.ofFn coreChunks345_4).flatten =
      (coreData345.take (coreResources345 4).q).drop 43 := by
  decide +kernel

theorem coreCheck345_4 :
    ∀ c : Fin 1, (coreChunks345_4 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 4)) = true := by
  decide +kernel
#print axioms coreFlatten345_4
#print axioms coreCheck345_4
end Erdos883Verified
