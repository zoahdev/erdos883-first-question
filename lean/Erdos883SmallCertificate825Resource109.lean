import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_109 :
    (List.ofFn coreChunks825_109).flatten =
      (coreData825.take (coreResources825 109).q).drop 197 := by
  decide +kernel

theorem coreCheck825_109 :
    ∀ c : Fin 1, (coreChunks825_109 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 109)) = true := by
  decide +kernel
#print axioms coreFlatten825_109
#print axioms coreCheck825_109
end Erdos883Verified
