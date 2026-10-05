import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_62 :
    (List.ofFn coreChunks825_62).flatten =
      (coreData825.take (coreResources825 62).q).drop 121 := by
  decide +kernel

theorem coreCheck825_62 :
    ∀ c : Fin 1, (coreChunks825_62 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 62)) = true := by
  decide +kernel
#print axioms coreFlatten825_62
#print axioms coreCheck825_62
end Erdos883Verified
