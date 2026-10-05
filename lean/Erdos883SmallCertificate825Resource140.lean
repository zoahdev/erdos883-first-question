import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_140 :
    (List.ofFn coreChunks825_140).flatten =
      (coreData825.take (coreResources825 140).q).drop 335 := by
  decide +kernel

theorem coreCheck825_140 :
    ∀ c : Fin 1, (coreChunks825_140 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 140)) = true := by
  decide +kernel
#print axioms coreFlatten825_140
#print axioms coreCheck825_140
end Erdos883Verified
