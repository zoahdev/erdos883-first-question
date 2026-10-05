import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_43 :
    (List.ofFn coreChunks825_43).flatten =
      (coreData825.take (coreResources825 43).q).drop 183 := by
  decide +kernel

theorem coreCheck825_43 :
    ∀ c : Fin 1, (coreChunks825_43 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 43)) = true := by
  decide +kernel
#print axioms coreFlatten825_43
#print axioms coreCheck825_43
end Erdos883Verified
