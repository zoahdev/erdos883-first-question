import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_84 :
    (List.ofFn coreChunks825_84).flatten =
      (coreData825.take (coreResources825 84).q).drop 152 := by
  decide +kernel

theorem coreCheck825_84 :
    ∀ c : Fin 1, (coreChunks825_84 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 84)) = true := by
  decide +kernel
#print axioms coreFlatten825_84
#print axioms coreCheck825_84
end Erdos883Verified
