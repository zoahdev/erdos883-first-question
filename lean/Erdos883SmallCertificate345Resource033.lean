import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_33 :
    (List.ofFn coreChunks345_33).flatten =
      (coreData345.take (coreResources345 33).q).drop 66 := by
  decide +kernel

theorem coreCheck345_33 :
    ∀ c : Fin 1, (coreChunks345_33 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 33)) = true := by
  decide +kernel
#print axioms coreFlatten345_33
#print axioms coreCheck345_33
end Erdos883Verified
