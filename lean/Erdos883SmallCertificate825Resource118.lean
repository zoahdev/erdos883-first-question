import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_118 :
    (List.ofFn coreChunks825_118).flatten =
      (coreData825.take (coreResources825 118).q).drop 214 := by
  decide +kernel

theorem coreCheck825_118 :
    ∀ c : Fin 1, (coreChunks825_118 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 118)) = true := by
  decide +kernel
#print axioms coreFlatten825_118
#print axioms coreCheck825_118
end Erdos883Verified
