import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_69 :
    (List.ofFn coreChunks825_69).flatten =
      (coreData825.take (coreResources825 69).q).drop 130 := by
  decide +kernel

theorem coreCheck825_69 :
    ∀ c : Fin 1, (coreChunks825_69 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 69)) = true := by
  decide +kernel
#print axioms coreFlatten825_69
#print axioms coreCheck825_69
end Erdos883Verified
