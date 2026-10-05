import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_50 :
    (List.ofFn coreChunks825_50).flatten =
      (coreData825.take (coreResources825 50).q).drop 197 := by
  decide +kernel

theorem coreCheck825_50 :
    ∀ c : Fin 1, (coreChunks825_50 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 50)) = true := by
  decide +kernel
#print axioms coreFlatten825_50
#print axioms coreCheck825_50
end Erdos883Verified
