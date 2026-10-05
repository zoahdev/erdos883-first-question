import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_21 :
    (List.ofFn coreChunks345_21).flatten =
      (coreData345.take (coreResources345 21).q).drop 0 := by
  decide +kernel

theorem coreCheck345_21 :
    ∀ c : Fin 3, (coreChunks345_21 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 21)) = true := by
  decide +kernel
#print axioms coreFlatten345_21
#print axioms coreCheck345_21
end Erdos883Verified
