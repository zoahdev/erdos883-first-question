import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_4 :
    (List.ofFn coreChunks825_4).flatten =
      (coreData825.take (coreResources825 4).q).drop 102 := by
  decide +kernel

theorem coreCheck825_4 :
    ∀ c : Fin 1, (coreChunks825_4 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 4)) = true := by
  decide +kernel
#print axioms coreFlatten825_4
#print axioms coreCheck825_4
end Erdos883Verified
