import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_12 :
    (List.ofFn coreChunks825_12).flatten =
      (coreData825.take (coreResources825 12).q).drop 144 := by
  decide +kernel

theorem coreCheck825_12 :
    ∀ c : Fin 1, (coreChunks825_12 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 12)) = true := by
  decide +kernel
#print axioms coreFlatten825_12
#print axioms coreCheck825_12
end Erdos883Verified
