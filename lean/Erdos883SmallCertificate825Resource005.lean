import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_5 :
    (List.ofFn coreChunks825_5).flatten =
      (coreData825.take (coreResources825 5).q).drop 103 := by
  decide +kernel

theorem coreCheck825_5 :
    ∀ c : Fin 1, (coreChunks825_5 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 5)) = true := by
  decide +kernel
#print axioms coreFlatten825_5
#print axioms coreCheck825_5
end Erdos883Verified
