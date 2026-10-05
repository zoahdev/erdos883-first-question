import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_75 :
    (List.ofFn coreChunks825_75).flatten =
      (coreData825.take (coreResources825 75).q).drop 137 := by
  decide +kernel

theorem coreCheck825_75 :
    ∀ c : Fin 1, (coreChunks825_75 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 75)) = true := by
  decide +kernel
#print axioms coreFlatten825_75
#print axioms coreCheck825_75
end Erdos883Verified
