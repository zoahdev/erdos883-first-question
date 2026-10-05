import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_51 :
    (List.ofFn coreChunks825_51).flatten =
      (coreData825.take (coreResources825 51).q).drop 198 := by
  decide +kernel

theorem coreCheck825_51 :
    ∀ c : Fin 1, (coreChunks825_51 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 51)) = true := by
  decide +kernel
#print axioms coreFlatten825_51
#print axioms coreCheck825_51
end Erdos883Verified
