import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_73 :
    (List.ofFn coreChunks825_73).flatten =
      (coreData825.take (coreResources825 73).q).drop 134 := by
  decide +kernel

theorem coreCheck825_73 :
    ∀ c : Fin 1, (coreChunks825_73 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 73)) = true := by
  decide +kernel
#print axioms coreFlatten825_73
#print axioms coreCheck825_73
end Erdos883Verified
