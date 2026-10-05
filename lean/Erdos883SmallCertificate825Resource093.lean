import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_93 :
    (List.ofFn coreChunks825_93).flatten =
      (coreData825.take (coreResources825 93).q).drop 167 := by
  decide +kernel

theorem coreCheck825_93 :
    ∀ c : Fin 1, (coreChunks825_93 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 93)) = true := by
  decide +kernel
#print axioms coreFlatten825_93
#print axioms coreCheck825_93
end Erdos883Verified
