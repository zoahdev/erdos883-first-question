import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_145 :
    (List.ofFn coreChunks825_145).flatten =
      (coreData825.take (coreResources825 145).q).drop 348 := by
  decide +kernel

theorem coreCheck825_145 :
    ∀ c : Fin 1, (coreChunks825_145 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 145)) = true := by
  decide +kernel
#print axioms coreFlatten825_145
#print axioms coreCheck825_145
end Erdos883Verified
