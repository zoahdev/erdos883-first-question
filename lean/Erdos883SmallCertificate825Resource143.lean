import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_143 :
    (List.ofFn coreChunks825_143).flatten =
      (coreData825.take (coreResources825 143).q).drop 344 := by
  decide +kernel

theorem coreCheck825_143 :
    ∀ c : Fin 1, (coreChunks825_143 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 143)) = true := by
  decide +kernel
#print axioms coreFlatten825_143
#print axioms coreCheck825_143
end Erdos883Verified
