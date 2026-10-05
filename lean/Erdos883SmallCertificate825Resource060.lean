import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_60 :
    (List.ofFn coreChunks825_60).flatten =
      (coreData825.take (coreResources825 60).q).drop 115 := by
  decide +kernel

theorem coreCheck825_60 :
    ∀ c : Fin 1, (coreChunks825_60 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 60)) = true := by
  decide +kernel
#print axioms coreFlatten825_60
#print axioms coreCheck825_60
end Erdos883Verified
