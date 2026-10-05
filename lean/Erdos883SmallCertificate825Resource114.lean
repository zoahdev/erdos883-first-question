import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_114 :
    (List.ofFn coreChunks825_114).flatten =
      (coreData825.take (coreResources825 114).q).drop 209 := by
  decide +kernel

theorem coreCheck825_114 :
    ∀ c : Fin 1, (coreChunks825_114 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 114)) = true := by
  decide +kernel
#print axioms coreFlatten825_114
#print axioms coreCheck825_114
end Erdos883Verified
