import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_124 :
    (List.ofFn coreChunks825_124).flatten =
      (coreData825.take (coreResources825 124).q).drop 236 := by
  decide +kernel

theorem coreCheck825_124 :
    ∀ c : Fin 1, (coreChunks825_124 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 124)) = true := by
  decide +kernel
#print axioms coreFlatten825_124
#print axioms coreCheck825_124
end Erdos883Verified
