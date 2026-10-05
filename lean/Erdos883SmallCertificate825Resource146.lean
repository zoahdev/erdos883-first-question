import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_146 :
    (List.ofFn coreChunks825_146).flatten =
      (coreData825.take (coreResources825 146).q).drop 351 := by
  decide +kernel

theorem coreCheck825_146 :
    ∀ c : Fin 1, (coreChunks825_146 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 146)) = true := by
  decide +kernel
#print axioms coreFlatten825_146
#print axioms coreCheck825_146
end Erdos883Verified
