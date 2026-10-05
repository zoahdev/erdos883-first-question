import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_152 :
    (List.ofFn coreChunks825_152).flatten =
      (coreData825.take (coreResources825 152).q).drop 263 := by
  decide +kernel

theorem coreCheck825_152 :
    ∀ c : Fin 1, (coreChunks825_152 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 152)) = true := by
  decide +kernel
#print axioms coreFlatten825_152
#print axioms coreCheck825_152
end Erdos883Verified
