import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_17 :
    (List.ofFn coreChunks825_17).flatten =
      (coreData825.take (coreResources825 17).q).drop 151 := by
  decide +kernel

theorem coreCheck825_17 :
    ∀ c : Fin 1, (coreChunks825_17 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 17)) = true := by
  decide +kernel
#print axioms coreFlatten825_17
#print axioms coreCheck825_17
end Erdos883Verified
