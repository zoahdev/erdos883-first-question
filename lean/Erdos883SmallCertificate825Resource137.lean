import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_137 :
    (List.ofFn coreChunks825_137).flatten =
      (coreData825.take (coreResources825 137).q).drop 310 := by
  decide +kernel

theorem coreCheck825_137 :
    ∀ c : Fin 1, (coreChunks825_137 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 137)) = true := by
  decide +kernel
#print axioms coreFlatten825_137
#print axioms coreCheck825_137
end Erdos883Verified
