import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_134 :
    (List.ofFn coreChunks825_134).flatten =
      (coreData825.take (coreResources825 134).q).drop 270 := by
  decide +kernel

theorem coreCheck825_134 :
    ∀ c : Fin 1, (coreChunks825_134 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 134)) = true := by
  decide +kernel
#print axioms coreFlatten825_134
#print axioms coreCheck825_134
end Erdos883Verified
