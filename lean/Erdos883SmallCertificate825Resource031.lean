import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_31 :
    (List.ofFn coreChunks825_31).flatten =
      (coreData825.take (coreResources825 31).q).drop 167 := by
  decide +kernel

theorem coreCheck825_31 :
    ∀ c : Fin 1, (coreChunks825_31 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 31)) = true := by
  decide +kernel
#print axioms coreFlatten825_31
#print axioms coreCheck825_31
end Erdos883Verified
