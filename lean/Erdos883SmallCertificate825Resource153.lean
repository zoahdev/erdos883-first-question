import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_153 :
    (List.ofFn coreChunks825_153).flatten =
      (coreData825.take (coreResources825 153).q).drop 266 := by
  decide +kernel

theorem coreCheck825_153 :
    ∀ c : Fin 1, (coreChunks825_153 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 153)) = true := by
  decide +kernel
#print axioms coreFlatten825_153
#print axioms coreCheck825_153
end Erdos883Verified
