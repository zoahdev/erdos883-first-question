import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_127 :
    (List.ofFn coreChunks825_127).flatten =
      (coreData825.take (coreResources825 127).q).drop 247 := by
  decide +kernel

theorem coreCheck825_127 :
    ∀ c : Fin 1, (coreChunks825_127 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 127)) = true := by
  decide +kernel
#print axioms coreFlatten825_127
#print axioms coreCheck825_127
end Erdos883Verified
