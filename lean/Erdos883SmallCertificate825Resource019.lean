import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_19 :
    (List.ofFn coreChunks825_19).flatten =
      (coreData825.take (coreResources825 19).q).drop 153 := by
  decide +kernel

theorem coreCheck825_19 :
    ∀ c : Fin 1, (coreChunks825_19 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 19)) = true := by
  decide +kernel
#print axioms coreFlatten825_19
#print axioms coreCheck825_19
end Erdos883Verified
