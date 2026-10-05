import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_72 :
    (List.ofFn coreChunks825_72).flatten =
      (coreData825.take (coreResources825 72).q).drop 133 := by
  decide +kernel

theorem coreCheck825_72 :
    ∀ c : Fin 1, (coreChunks825_72 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 72)) = true := by
  decide +kernel
#print axioms coreFlatten825_72
#print axioms coreCheck825_72
end Erdos883Verified
