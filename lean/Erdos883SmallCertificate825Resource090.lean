import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_90 :
    (List.ofFn coreChunks825_90).flatten =
      (coreData825.take (coreResources825 90).q).drop 164 := by
  decide +kernel

theorem coreCheck825_90 :
    ∀ c : Fin 1, (coreChunks825_90 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 90)) = true := by
  decide +kernel
#print axioms coreFlatten825_90
#print axioms coreCheck825_90
end Erdos883Verified
