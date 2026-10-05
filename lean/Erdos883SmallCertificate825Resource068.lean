import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_68 :
    (List.ofFn coreChunks825_68).flatten =
      (coreData825.take (coreResources825 68).q).drop 129 := by
  decide +kernel

theorem coreCheck825_68 :
    ∀ c : Fin 1, (coreChunks825_68 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 68)) = true := by
  decide +kernel
#print axioms coreFlatten825_68
#print axioms coreCheck825_68
end Erdos883Verified
