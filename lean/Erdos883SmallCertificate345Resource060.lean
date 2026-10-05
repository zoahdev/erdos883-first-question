import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_60 :
    (List.ofFn coreChunks345_60).flatten =
      (coreData345.take (coreResources345 60).q).drop 129 := by
  decide +kernel

theorem coreCheck345_60 :
    ∀ c : Fin 1, (coreChunks345_60 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 60)) = true := by
  decide +kernel
#print axioms coreFlatten345_60
#print axioms coreCheck345_60
end Erdos883Verified
