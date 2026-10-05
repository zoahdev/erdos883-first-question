import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_35 :
    (List.ofFn coreChunks345_35).flatten =
      (coreData345.take (coreResources345 35).q).drop 69 := by
  decide +kernel

theorem coreCheck345_35 :
    ∀ c : Fin 1, (coreChunks345_35 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 35)) = true := by
  decide +kernel
#print axioms coreFlatten345_35
#print axioms coreCheck345_35
end Erdos883Verified
