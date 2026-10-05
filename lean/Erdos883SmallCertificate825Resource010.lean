import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_10 :
    (List.ofFn coreChunks825_10).flatten =
      (coreData825.take (coreResources825 10).q).drop 142 := by
  decide +kernel

theorem coreCheck825_10 :
    ∀ c : Fin 1, (coreChunks825_10 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 10)) = true := by
  decide +kernel
#print axioms coreFlatten825_10
#print axioms coreCheck825_10
end Erdos883Verified
