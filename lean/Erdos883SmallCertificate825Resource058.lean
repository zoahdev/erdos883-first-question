import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_58 :
    (List.ofFn coreChunks825_58).flatten =
      (coreData825.take (coreResources825 58).q).drop 103 := by
  decide +kernel

theorem coreCheck825_58 :
    ∀ c : Fin 1, (coreChunks825_58 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 58)) = true := by
  decide +kernel
#print axioms coreFlatten825_58
#print axioms coreCheck825_58
end Erdos883Verified
