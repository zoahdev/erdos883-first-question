import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_7 :
    (List.ofFn coreChunks825_7).flatten =
      (coreData825.take (coreResources825 7).q).drop 110 := by
  decide +kernel

theorem coreCheck825_7 :
    ∀ c : Fin 2, (coreChunks825_7 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 7)) = true := by
  decide +kernel
#print axioms coreFlatten825_7
#print axioms coreCheck825_7
end Erdos883Verified
