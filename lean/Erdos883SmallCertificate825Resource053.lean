import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_53 :
    (List.ofFn coreChunks825_53).flatten =
      (coreData825.take (coreResources825 53).q).drop 203 := by
  decide +kernel

theorem coreCheck825_53 :
    ∀ c : Fin 1, (coreChunks825_53 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 53)) = true := by
  decide +kernel
#print axioms coreFlatten825_53
#print axioms coreCheck825_53
end Erdos883Verified
