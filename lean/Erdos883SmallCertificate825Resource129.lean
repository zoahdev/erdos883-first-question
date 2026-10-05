import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_129 :
    (List.ofFn coreChunks825_129).flatten =
      (coreData825.take (coreResources825 129).q).drop 251 := by
  decide +kernel

theorem coreCheck825_129 :
    ∀ c : Fin 1, (coreChunks825_129 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 129)) = true := by
  decide +kernel
#print axioms coreFlatten825_129
#print axioms coreCheck825_129
end Erdos883Verified
