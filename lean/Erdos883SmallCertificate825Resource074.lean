import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_74 :
    (List.ofFn coreChunks825_74).flatten =
      (coreData825.take (coreResources825 74).q).drop 135 := by
  decide +kernel

theorem coreCheck825_74 :
    ∀ c : Fin 1, (coreChunks825_74 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 74)) = true := by
  decide +kernel
#print axioms coreFlatten825_74
#print axioms coreCheck825_74
end Erdos883Verified
