import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_55 :
    (List.ofFn coreChunks825_55).flatten =
      (coreData825.take (coreResources825 55).q).drop 206 := by
  decide +kernel

theorem coreCheck825_55 :
    ∀ c : Fin 1, (coreChunks825_55 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 55)) = true := by
  decide +kernel
#print axioms coreFlatten825_55
#print axioms coreCheck825_55
end Erdos883Verified
