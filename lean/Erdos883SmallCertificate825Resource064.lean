import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_64 :
    (List.ofFn coreChunks825_64).flatten =
      (coreData825.take (coreResources825 64).q).drop 124 := by
  decide +kernel

theorem coreCheck825_64 :
    ∀ c : Fin 1, (coreChunks825_64 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 64)) = true := by
  decide +kernel
#print axioms coreFlatten825_64
#print axioms coreCheck825_64
end Erdos883Verified
