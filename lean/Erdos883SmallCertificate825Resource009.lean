import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_9 :
    (List.ofFn coreChunks825_9).flatten =
      (coreData825.take (coreResources825 9).q).drop 141 := by
  decide +kernel

theorem coreCheck825_9 :
    ∀ c : Fin 1, (coreChunks825_9 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 9)) = true := by
  decide +kernel
#print axioms coreFlatten825_9
#print axioms coreCheck825_9
end Erdos883Verified
