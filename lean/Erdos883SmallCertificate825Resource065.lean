import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_65 :
    (List.ofFn coreChunks825_65).flatten =
      (coreData825.take (coreResources825 65).q).drop 126 := by
  decide +kernel

theorem coreCheck825_65 :
    ∀ c : Fin 1, (coreChunks825_65 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 65)) = true := by
  decide +kernel
#print axioms coreFlatten825_65
#print axioms coreCheck825_65
end Erdos883Verified
