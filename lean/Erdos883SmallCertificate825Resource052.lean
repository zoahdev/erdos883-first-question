import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_52 :
    (List.ofFn coreChunks825_52).flatten =
      (coreData825.take (coreResources825 52).q).drop 200 := by
  decide +kernel

theorem coreCheck825_52 :
    ∀ c : Fin 1, (coreChunks825_52 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 52)) = true := by
  decide +kernel
#print axioms coreFlatten825_52
#print axioms coreCheck825_52
end Erdos883Verified
