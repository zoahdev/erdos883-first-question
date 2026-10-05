import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_120 :
    (List.ofFn coreChunks825_120).flatten =
      (coreData825.take (coreResources825 120).q).drop 216 := by
  decide +kernel

theorem coreCheck825_120 :
    ∀ c : Fin 1, (coreChunks825_120 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 120)) = true := by
  decide +kernel
#print axioms coreFlatten825_120
#print axioms coreCheck825_120
end Erdos883Verified
