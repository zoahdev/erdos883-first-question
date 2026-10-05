import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_19 :
    (List.ofFn coreChunks345_19).flatten =
      (coreData345.take (coreResources345 19).q).drop 85 := by
  decide +kernel

theorem coreCheck345_19 :
    ∀ c : Fin 1, (coreChunks345_19 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 19)) = true := by
  decide +kernel
#print axioms coreFlatten345_19
#print axioms coreCheck345_19
end Erdos883Verified
