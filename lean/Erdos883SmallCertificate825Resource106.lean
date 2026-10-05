import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_106 :
    (List.ofFn coreChunks825_106).flatten =
      (coreData825.take (coreResources825 106).q).drop 187 := by
  decide +kernel

theorem coreCheck825_106 :
    ∀ c : Fin 1, (coreChunks825_106 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 106)) = true := by
  decide +kernel
#print axioms coreFlatten825_106
#print axioms coreCheck825_106
end Erdos883Verified
