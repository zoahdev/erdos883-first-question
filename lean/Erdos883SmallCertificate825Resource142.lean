import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_142 :
    (List.ofFn coreChunks825_142).flatten =
      (coreData825.take (coreResources825 142).q).drop 339 := by
  decide +kernel

theorem coreCheck825_142 :
    ∀ c : Fin 1, (coreChunks825_142 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 142)) = true := by
  decide +kernel
#print axioms coreFlatten825_142
#print axioms coreCheck825_142
end Erdos883Verified
