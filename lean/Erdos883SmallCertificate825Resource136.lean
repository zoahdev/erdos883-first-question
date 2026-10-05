import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_136 :
    (List.ofFn coreChunks825_136).flatten =
      (coreData825.take (coreResources825 136).q).drop 292 := by
  decide +kernel

theorem coreCheck825_136 :
    ∀ c : Fin 2, (coreChunks825_136 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 136)) = true := by
  decide +kernel
#print axioms coreFlatten825_136
#print axioms coreCheck825_136
end Erdos883Verified
