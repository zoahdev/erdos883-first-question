import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_26 :
    (List.ofFn coreChunks825_26).flatten =
      (coreData825.take (coreResources825 26).q).drop 162 := by
  decide +kernel

theorem coreCheck825_26 :
    ∀ c : Fin 1, (coreChunks825_26 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 26)) = true := by
  decide +kernel
#print axioms coreFlatten825_26
#print axioms coreCheck825_26
end Erdos883Verified
