import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_40 :
    (List.ofFn coreChunks825_40).flatten =
      (coreData825.take (coreResources825 40).q).drop 180 := by
  decide +kernel

theorem coreCheck825_40 :
    ∀ c : Fin 1, (coreChunks825_40 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 40)) = true := by
  decide +kernel
#print axioms coreFlatten825_40
#print axioms coreCheck825_40
end Erdos883Verified
