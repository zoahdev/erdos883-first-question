import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_110 :
    (List.ofFn coreChunks825_110).flatten =
      (coreData825.take (coreResources825 110).q).drop 200 := by
  decide +kernel

theorem coreCheck825_110 :
    ∀ c : Fin 1, (coreChunks825_110 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 110)) = true := by
  decide +kernel
#print axioms coreFlatten825_110
#print axioms coreCheck825_110
end Erdos883Verified
