import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_32 :
    (List.ofFn coreChunks825_32).flatten =
      (coreData825.take (coreResources825 32).q).drop 170 := by
  decide +kernel

theorem coreCheck825_32 :
    ∀ c : Fin 1, (coreChunks825_32 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 32)) = true := by
  decide +kernel
#print axioms coreFlatten825_32
#print axioms coreCheck825_32
end Erdos883Verified
