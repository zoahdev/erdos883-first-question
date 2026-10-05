import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_92 :
    (List.ofFn coreChunks825_92).flatten =
      (coreData825.take (coreResources825 92).q).drop 166 := by
  decide +kernel

theorem coreCheck825_92 :
    ∀ c : Fin 1, (coreChunks825_92 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 92)) = true := by
  decide +kernel
#print axioms coreFlatten825_92
#print axioms coreCheck825_92
end Erdos883Verified
