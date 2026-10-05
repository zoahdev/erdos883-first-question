import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_80 :
    (List.ofFn coreChunks825_80).flatten =
      (coreData825.take (coreResources825 80).q).drop 147 := by
  decide +kernel

theorem coreCheck825_80 :
    ∀ c : Fin 1, (coreChunks825_80 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 80)) = true := by
  decide +kernel
#print axioms coreFlatten825_80
#print axioms coreCheck825_80
end Erdos883Verified
