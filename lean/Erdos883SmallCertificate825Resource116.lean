import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_116 :
    (List.ofFn coreChunks825_116).flatten =
      (coreData825.take (coreResources825 116).q).drop 211 := by
  decide +kernel

theorem coreCheck825_116 :
    ∀ c : Fin 1, (coreChunks825_116 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 116)) = true := by
  decide +kernel
#print axioms coreFlatten825_116
#print axioms coreCheck825_116
end Erdos883Verified
