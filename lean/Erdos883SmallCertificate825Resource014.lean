import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_14 :
    (List.ofFn coreChunks825_14).flatten =
      (coreData825.take (coreResources825 14).q).drop 148 := by
  decide +kernel

theorem coreCheck825_14 :
    ∀ c : Fin 1, (coreChunks825_14 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 14)) = true := by
  decide +kernel
#print axioms coreFlatten825_14
#print axioms coreCheck825_14
end Erdos883Verified
