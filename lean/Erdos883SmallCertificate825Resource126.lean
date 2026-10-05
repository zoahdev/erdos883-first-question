import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_126 :
    (List.ofFn coreChunks825_126).flatten =
      (coreData825.take (coreResources825 126).q).drop 246 := by
  decide +kernel

theorem coreCheck825_126 :
    ∀ c : Fin 1, (coreChunks825_126 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 126)) = true := by
  decide +kernel
#print axioms coreFlatten825_126
#print axioms coreCheck825_126
end Erdos883Verified
