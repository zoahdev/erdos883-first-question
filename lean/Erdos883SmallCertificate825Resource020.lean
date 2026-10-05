import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_20 :
    (List.ofFn coreChunks825_20).flatten =
      (coreData825.take (coreResources825 20).q).drop 154 := by
  decide +kernel

theorem coreCheck825_20 :
    ∀ c : Fin 1, (coreChunks825_20 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 20)) = true := by
  decide +kernel
#print axioms coreFlatten825_20
#print axioms coreCheck825_20
end Erdos883Verified
