import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_98 :
    (List.ofFn coreChunks825_98).flatten =
      (coreData825.take (coreResources825 98).q).drop 178 := by
  decide +kernel

theorem coreCheck825_98 :
    ∀ c : Fin 1, (coreChunks825_98 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 98)) = true := by
  decide +kernel
#print axioms coreFlatten825_98
#print axioms coreCheck825_98
end Erdos883Verified
