import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_123 :
    (List.ofFn coreChunks825_123).flatten =
      (coreData825.take (coreResources825 123).q).drop 234 := by
  decide +kernel

theorem coreCheck825_123 :
    ∀ c : Fin 1, (coreChunks825_123 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 123)) = true := by
  decide +kernel
#print axioms coreFlatten825_123
#print axioms coreCheck825_123
end Erdos883Verified
