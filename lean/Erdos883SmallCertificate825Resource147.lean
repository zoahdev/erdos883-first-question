import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_147 :
    (List.ofFn coreChunks825_147).flatten =
      (coreData825.take (coreResources825 147).q).drop 354 := by
  decide +kernel

theorem coreCheck825_147 :
    ∀ c : Fin 1, (coreChunks825_147 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 147)) = true := by
  decide +kernel
#print axioms coreFlatten825_147
#print axioms coreCheck825_147
end Erdos883Verified
