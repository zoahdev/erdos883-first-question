import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_29 :
    (List.ofFn coreChunks825_29).flatten =
      (coreData825.take (coreResources825 29).q).drop 165 := by
  decide +kernel

theorem coreCheck825_29 :
    ∀ c : Fin 1, (coreChunks825_29 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 29)) = true := by
  decide +kernel
#print axioms coreFlatten825_29
#print axioms coreCheck825_29
end Erdos883Verified
