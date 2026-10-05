import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_121 :
    (List.ofFn coreChunks825_121).flatten =
      (coreData825.take (coreResources825 121).q).drop 220 := by
  decide +kernel

theorem coreCheck825_121 :
    ∀ c : Fin 1, (coreChunks825_121 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 121)) = true := by
  decide +kernel
#print axioms coreFlatten825_121
#print axioms coreCheck825_121
end Erdos883Verified
