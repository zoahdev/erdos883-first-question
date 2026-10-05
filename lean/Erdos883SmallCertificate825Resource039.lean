import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_39 :
    (List.ofFn coreChunks825_39).flatten =
      (coreData825.take (coreResources825 39).q).drop 179 := by
  decide +kernel

theorem coreCheck825_39 :
    ∀ c : Fin 1, (coreChunks825_39 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 39)) = true := by
  decide +kernel
#print axioms coreFlatten825_39
#print axioms coreCheck825_39
end Erdos883Verified
