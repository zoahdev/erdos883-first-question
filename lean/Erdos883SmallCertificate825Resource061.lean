import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_61 :
    (List.ofFn coreChunks825_61).flatten =
      (coreData825.take (coreResources825 61).q).drop 120 := by
  decide +kernel

theorem coreCheck825_61 :
    ∀ c : Fin 1, (coreChunks825_61 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 61)) = true := by
  decide +kernel
#print axioms coreFlatten825_61
#print axioms coreCheck825_61
end Erdos883Verified
