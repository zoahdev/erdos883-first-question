import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_101 :
    (List.ofFn coreChunks825_101).flatten =
      (coreData825.take (coreResources825 101).q).drop 181 := by
  decide +kernel

theorem coreCheck825_101 :
    ∀ c : Fin 1, (coreChunks825_101 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 101)) = true := by
  decide +kernel
#print axioms coreFlatten825_101
#print axioms coreCheck825_101
end Erdos883Verified
