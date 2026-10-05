import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_43 :
    (List.ofFn coreChunks345_43).flatten =
      (coreData345.take (coreResources345 43).q).drop 84 := by
  decide +kernel

theorem coreCheck345_43 :
    ∀ c : Fin 1, (coreChunks345_43 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 43)) = true := by
  decide +kernel
#print axioms coreFlatten345_43
#print axioms coreCheck345_43
end Erdos883Verified
