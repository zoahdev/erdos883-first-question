import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_117 :
    (List.ofFn coreChunks825_117).flatten =
      (coreData825.take (coreResources825 117).q).drop 213 := by
  decide +kernel

theorem coreCheck825_117 :
    ∀ c : Fin 1, (coreChunks825_117 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 117)) = true := by
  decide +kernel
#print axioms coreFlatten825_117
#print axioms coreCheck825_117
end Erdos883Verified
