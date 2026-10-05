import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_66 :
    (List.ofFn coreChunks825_66).flatten =
      (coreData825.take (coreResources825 66).q).drop 127 := by
  decide +kernel

theorem coreCheck825_66 :
    ∀ c : Fin 1, (coreChunks825_66 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 66)) = true := by
  decide +kernel
#print axioms coreFlatten825_66
#print axioms coreCheck825_66
end Erdos883Verified
