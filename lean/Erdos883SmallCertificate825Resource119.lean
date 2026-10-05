import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_119 :
    (List.ofFn coreChunks825_119).flatten =
      (coreData825.take (coreResources825 119).q).drop 215 := by
  decide +kernel

theorem coreCheck825_119 :
    ∀ c : Fin 1, (coreChunks825_119 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 119)) = true := by
  decide +kernel
#print axioms coreFlatten825_119
#print axioms coreCheck825_119
end Erdos883Verified
