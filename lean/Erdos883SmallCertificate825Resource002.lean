import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_2 :
    (List.ofFn coreChunks825_2).flatten =
      (coreData825.take (coreResources825 2).q).drop 91 := by
  decide +kernel

theorem coreCheck825_2 :
    ∀ c : Fin 1, (coreChunks825_2 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 2)) = true := by
  decide +kernel
#print axioms coreFlatten825_2
#print axioms coreCheck825_2
end Erdos883Verified
