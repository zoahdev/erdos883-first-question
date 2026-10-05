import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_21 :
    (List.ofFn coreChunks825_21).flatten =
      (coreData825.take (coreResources825 21).q).drop 155 := by
  decide +kernel

theorem coreCheck825_21 :
    ∀ c : Fin 1, (coreChunks825_21 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 21)) = true := by
  decide +kernel
#print axioms coreFlatten825_21
#print axioms coreCheck825_21
end Erdos883Verified
