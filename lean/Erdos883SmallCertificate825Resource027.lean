import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_27 :
    (List.ofFn coreChunks825_27).flatten =
      (coreData825.take (coreResources825 27).q).drop 163 := by
  decide +kernel

theorem coreCheck825_27 :
    ∀ c : Fin 1, (coreChunks825_27 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 27)) = true := by
  decide +kernel
#print axioms coreFlatten825_27
#print axioms coreCheck825_27
end Erdos883Verified
