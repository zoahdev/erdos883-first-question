import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_113 :
    (List.ofFn coreChunks825_113).flatten =
      (coreData825.take (coreResources825 113).q).drop 208 := by
  decide +kernel

theorem coreCheck825_113 :
    ∀ c : Fin 1, (coreChunks825_113 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 113)) = true := by
  decide +kernel
#print axioms coreFlatten825_113
#print axioms coreCheck825_113
end Erdos883Verified
