import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_18 :
    (List.ofFn coreChunks825_18).flatten =
      (coreData825.take (coreResources825 18).q).drop 152 := by
  decide +kernel

theorem coreCheck825_18 :
    ∀ c : Fin 1, (coreChunks825_18 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 18)) = true := by
  decide +kernel
#print axioms coreFlatten825_18
#print axioms coreCheck825_18
end Erdos883Verified
