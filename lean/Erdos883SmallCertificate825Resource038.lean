import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_38 :
    (List.ofFn coreChunks825_38).flatten =
      (coreData825.take (coreResources825 38).q).drop 178 := by
  decide +kernel

theorem coreCheck825_38 :
    ∀ c : Fin 1, (coreChunks825_38 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 38)) = true := by
  decide +kernel
#print axioms coreFlatten825_38
#print axioms coreCheck825_38
end Erdos883Verified
