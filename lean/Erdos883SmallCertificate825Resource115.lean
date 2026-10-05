import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_115 :
    (List.ofFn coreChunks825_115).flatten =
      (coreData825.take (coreResources825 115).q).drop 210 := by
  decide +kernel

theorem coreCheck825_115 :
    ∀ c : Fin 1, (coreChunks825_115 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 115)) = true := by
  decide +kernel
#print axioms coreFlatten825_115
#print axioms coreCheck825_115
end Erdos883Verified
