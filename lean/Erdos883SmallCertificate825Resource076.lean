import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_76 :
    (List.ofFn coreChunks825_76).flatten =
      (coreData825.take (coreResources825 76).q).drop 139 := by
  decide +kernel

theorem coreCheck825_76 :
    ∀ c : Fin 1, (coreChunks825_76 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 76)) = true := by
  decide +kernel
#print axioms coreFlatten825_76
#print axioms coreCheck825_76
end Erdos883Verified
