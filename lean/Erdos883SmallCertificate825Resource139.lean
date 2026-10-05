import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_139 :
    (List.ofFn coreChunks825_139).flatten =
      (coreData825.take (coreResources825 139).q).drop 331 := by
  decide +kernel

theorem coreCheck825_139 :
    ∀ c : Fin 1, (coreChunks825_139 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 139)) = true := by
  decide +kernel
#print axioms coreFlatten825_139
#print axioms coreCheck825_139
end Erdos883Verified
