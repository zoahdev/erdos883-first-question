import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_57 :
    (List.ofFn coreChunks825_57).flatten =
      (coreData825.take (coreResources825 57).q).drop 102 := by
  decide +kernel

theorem coreCheck825_57 :
    ∀ c : Fin 1, (coreChunks825_57 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 57)) = true := by
  decide +kernel
#print axioms coreFlatten825_57
#print axioms coreCheck825_57
end Erdos883Verified
