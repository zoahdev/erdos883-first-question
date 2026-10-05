import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_85 :
    (List.ofFn coreChunks825_85).flatten =
      (coreData825.take (coreResources825 85).q).drop 154 := by
  decide +kernel

theorem coreCheck825_85 :
    ∀ c : Fin 1, (coreChunks825_85 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 85)) = true := by
  decide +kernel
#print axioms coreFlatten825_85
#print axioms coreCheck825_85
end Erdos883Verified
