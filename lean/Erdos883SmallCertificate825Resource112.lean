import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_112 :
    (List.ofFn coreChunks825_112).flatten =
      (coreData825.take (coreResources825 112).q).drop 206 := by
  decide +kernel

theorem coreCheck825_112 :
    ∀ c : Fin 1, (coreChunks825_112 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 112)) = true := by
  decide +kernel
#print axioms coreFlatten825_112
#print axioms coreCheck825_112
end Erdos883Verified
