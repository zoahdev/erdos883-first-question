import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_95 :
    (List.ofFn coreChunks825_95).flatten =
      (coreData825.take (coreResources825 95).q).drop 172 := by
  decide +kernel

theorem coreCheck825_95 :
    ∀ c : Fin 1, (coreChunks825_95 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 95)) = true := by
  decide +kernel
#print axioms coreFlatten825_95
#print axioms coreCheck825_95
end Erdos883Verified
