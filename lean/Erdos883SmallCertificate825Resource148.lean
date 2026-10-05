import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_148 :
    (List.ofFn coreChunks825_148).flatten =
      (coreData825.take (coreResources825 148).q).drop 355 := by
  decide +kernel

theorem coreCheck825_148 :
    ∀ c : Fin 1, (coreChunks825_148 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 148)) = true := by
  decide +kernel
#print axioms coreFlatten825_148
#print axioms coreCheck825_148
end Erdos883Verified
