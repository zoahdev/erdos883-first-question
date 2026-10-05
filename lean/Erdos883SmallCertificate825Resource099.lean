import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_99 :
    (List.ofFn coreChunks825_99).flatten =
      (coreData825.take (coreResources825 99).q).drop 179 := by
  decide +kernel

theorem coreCheck825_99 :
    ∀ c : Fin 1, (coreChunks825_99 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 99)) = true := by
  decide +kernel
#print axioms coreFlatten825_99
#print axioms coreCheck825_99
end Erdos883Verified
