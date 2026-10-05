import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_78 :
    (List.ofFn coreChunks825_78).flatten =
      (coreData825.take (coreResources825 78).q).drop 142 := by
  decide +kernel

theorem coreCheck825_78 :
    ∀ c : Fin 1, (coreChunks825_78 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 78)) = true := by
  decide +kernel
#print axioms coreFlatten825_78
#print axioms coreCheck825_78
end Erdos883Verified
