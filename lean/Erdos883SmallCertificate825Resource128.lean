import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_128 :
    (List.ofFn coreChunks825_128).flatten =
      (coreData825.take (coreResources825 128).q).drop 248 := by
  decide +kernel

theorem coreCheck825_128 :
    ∀ c : Fin 1, (coreChunks825_128 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 128)) = true := by
  decide +kernel
#print axioms coreFlatten825_128
#print axioms coreCheck825_128
end Erdos883Verified
