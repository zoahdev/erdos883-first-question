import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_22 :
    (List.ofFn coreChunks825_22).flatten =
      (coreData825.take (coreResources825 22).q).drop 157 := by
  decide +kernel

theorem coreCheck825_22 :
    ∀ c : Fin 1, (coreChunks825_22 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 22)) = true := by
  decide +kernel
#print axioms coreFlatten825_22
#print axioms coreCheck825_22
end Erdos883Verified
