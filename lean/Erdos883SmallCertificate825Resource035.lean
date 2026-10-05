import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_35 :
    (List.ofFn coreChunks825_35).flatten =
      (coreData825.take (coreResources825 35).q).drop 174 := by
  decide +kernel

theorem coreCheck825_35 :
    ∀ c : Fin 1, (coreChunks825_35 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 35)) = true := by
  decide +kernel
#print axioms coreFlatten825_35
#print axioms coreCheck825_35
end Erdos883Verified
