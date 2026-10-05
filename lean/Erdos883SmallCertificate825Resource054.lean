import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_54 :
    (List.ofFn coreChunks825_54).flatten =
      (coreData825.take (coreResources825 54).q).drop 205 := by
  decide +kernel

theorem coreCheck825_54 :
    ∀ c : Fin 1, (coreChunks825_54 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 54)) = true := by
  decide +kernel
#print axioms coreFlatten825_54
#print axioms coreCheck825_54
end Erdos883Verified
