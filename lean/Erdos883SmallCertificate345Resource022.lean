import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_22 :
    (List.ofFn coreChunks345_22).flatten =
      (coreData345.take (coreResources345 22).q).drop 48 := by
  decide +kernel

theorem coreCheck345_22 :
    ∀ c : Fin 1, (coreChunks345_22 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 22)) = true := by
  decide +kernel
#print axioms coreFlatten345_22
#print axioms coreCheck345_22
end Erdos883Verified
