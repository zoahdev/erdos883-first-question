import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_102 :
    (List.ofFn coreChunks825_102).flatten =
      (coreData825.take (coreResources825 102).q).drop 183 := by
  decide +kernel

theorem coreCheck825_102 :
    ∀ c : Fin 1, (coreChunks825_102 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 102)) = true := by
  decide +kernel
#print axioms coreFlatten825_102
#print axioms coreCheck825_102
end Erdos883Verified
