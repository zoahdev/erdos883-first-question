import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_42 :
    (List.ofFn coreChunks825_42).flatten =
      (coreData825.take (coreResources825 42).q).drop 182 := by
  decide +kernel

theorem coreCheck825_42 :
    ∀ c : Fin 1, (coreChunks825_42 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 42)) = true := by
  decide +kernel
#print axioms coreFlatten825_42
#print axioms coreCheck825_42
end Erdos883Verified
