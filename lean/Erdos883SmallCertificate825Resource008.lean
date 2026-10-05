import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_8 :
    (List.ofFn coreChunks825_8).flatten =
      (coreData825.take (coreResources825 8).q).drop 139 := by
  decide +kernel

theorem coreCheck825_8 :
    ∀ c : Fin 1, (coreChunks825_8 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 8)) = true := by
  decide +kernel
#print axioms coreFlatten825_8
#print axioms coreCheck825_8
end Erdos883Verified
