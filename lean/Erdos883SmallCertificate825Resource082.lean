import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_82 :
    (List.ofFn coreChunks825_82).flatten =
      (coreData825.take (coreResources825 82).q).drop 150 := by
  decide +kernel

theorem coreCheck825_82 :
    ∀ c : Fin 1, (coreChunks825_82 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 82)) = true := by
  decide +kernel
#print axioms coreFlatten825_82
#print axioms coreCheck825_82
end Erdos883Verified
