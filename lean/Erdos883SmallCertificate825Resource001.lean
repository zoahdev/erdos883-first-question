import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_1 :
    (List.ofFn coreChunks825_1).flatten =
      (coreData825.take (coreResources825 1).q).drop 71 := by
  decide +kernel

theorem coreCheck825_1 :
    ∀ c : Fin 2, (coreChunks825_1 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 1)) = true := by
  decide +kernel
#print axioms coreFlatten825_1
#print axioms coreCheck825_1
end Erdos883Verified
