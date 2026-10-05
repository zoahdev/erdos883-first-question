import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_97 :
    (List.ofFn coreChunks825_97).flatten =
      (coreData825.take (coreResources825 97).q).drop 177 := by
  decide +kernel

theorem coreCheck825_97 :
    ∀ c : Fin 1, (coreChunks825_97 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 97)) = true := by
  decide +kernel
#print axioms coreFlatten825_97
#print axioms coreCheck825_97
end Erdos883Verified
