import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_122 :
    (List.ofFn coreChunks825_122).flatten =
      (coreData825.take (coreResources825 122).q).drop 228 := by
  decide +kernel

theorem coreCheck825_122 :
    ∀ c : Fin 1, (coreChunks825_122 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 122)) = true := by
  decide +kernel
#print axioms coreFlatten825_122
#print axioms coreCheck825_122
end Erdos883Verified
