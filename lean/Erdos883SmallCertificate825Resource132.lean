import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_132 :
    (List.ofFn coreChunks825_132).flatten =
      (coreData825.take (coreResources825 132).q).drop 261 := by
  decide +kernel

theorem coreCheck825_132 :
    ∀ c : Fin 1, (coreChunks825_132 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 132)) = true := by
  decide +kernel
#print axioms coreFlatten825_132
#print axioms coreCheck825_132
end Erdos883Verified
