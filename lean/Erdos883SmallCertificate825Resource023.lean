import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_23 :
    (List.ofFn coreChunks825_23).flatten =
      (coreData825.take (coreResources825 23).q).drop 158 := by
  decide +kernel

theorem coreCheck825_23 :
    ∀ c : Fin 1, (coreChunks825_23 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 23)) = true := by
  decide +kernel
#print axioms coreFlatten825_23
#print axioms coreCheck825_23
end Erdos883Verified
