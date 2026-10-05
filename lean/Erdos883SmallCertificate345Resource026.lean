import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_26 :
    (List.ofFn coreChunks345_26).flatten =
      (coreData345.take (coreResources345 26).q).drop 57 := by
  decide +kernel

theorem coreCheck345_26 :
    ∀ c : Fin 1, (coreChunks345_26 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 26)) = true := by
  decide +kernel
#print axioms coreFlatten345_26
#print axioms coreCheck345_26
end Erdos883Verified
