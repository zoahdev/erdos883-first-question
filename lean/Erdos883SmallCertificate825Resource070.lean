import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_70 :
    (List.ofFn coreChunks825_70).flatten =
      (coreData825.take (coreResources825 70).q).drop 131 := by
  decide +kernel

theorem coreCheck825_70 :
    ∀ c : Fin 1, (coreChunks825_70 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 70)) = true := by
  decide +kernel
#print axioms coreFlatten825_70
#print axioms coreCheck825_70
end Erdos883Verified
