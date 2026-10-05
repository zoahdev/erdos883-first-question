import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_41 :
    (List.ofFn coreChunks825_41).flatten =
      (coreData825.take (coreResources825 41).q).drop 181 := by
  decide +kernel

theorem coreCheck825_41 :
    ∀ c : Fin 1, (coreChunks825_41 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 41)) = true := by
  decide +kernel
#print axioms coreFlatten825_41
#print axioms coreCheck825_41
end Erdos883Verified
