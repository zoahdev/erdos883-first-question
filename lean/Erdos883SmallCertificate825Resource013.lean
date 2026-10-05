import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_13 :
    (List.ofFn coreChunks825_13).flatten =
      (coreData825.take (coreResources825 13).q).drop 147 := by
  decide +kernel

theorem coreCheck825_13 :
    ∀ c : Fin 1, (coreChunks825_13 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 13)) = true := by
  decide +kernel
#print axioms coreFlatten825_13
#print axioms coreCheck825_13
end Erdos883Verified
