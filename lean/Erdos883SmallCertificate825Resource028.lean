import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_28 :
    (List.ofFn coreChunks825_28).flatten =
      (coreData825.take (coreResources825 28).q).drop 164 := by
  decide +kernel

theorem coreCheck825_28 :
    ∀ c : Fin 1, (coreChunks825_28 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 28)) = true := by
  decide +kernel
#print axioms coreFlatten825_28
#print axioms coreCheck825_28
end Erdos883Verified
