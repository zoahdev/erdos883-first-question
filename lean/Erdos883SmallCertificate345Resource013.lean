import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_13 :
    (List.ofFn coreChunks345_13).flatten =
      (coreData345.take (coreResources345 13).q).drop 75 := by
  decide +kernel

theorem coreCheck345_13 :
    ∀ c : Fin 1, (coreChunks345_13 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 13)) = true := by
  decide +kernel
#print axioms coreFlatten345_13
#print axioms coreCheck345_13
end Erdos883Verified
