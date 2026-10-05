import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_103 :
    (List.ofFn coreChunks825_103).flatten =
      (coreData825.take (coreResources825 103).q).drop 184 := by
  decide +kernel

theorem coreCheck825_103 :
    ∀ c : Fin 1, (coreChunks825_103 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 103)) = true := by
  decide +kernel
#print axioms coreFlatten825_103
#print axioms coreCheck825_103
end Erdos883Verified
