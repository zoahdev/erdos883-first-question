import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_91 :
    (List.ofFn coreChunks825_91).flatten =
      (coreData825.take (coreResources825 91).q).drop 165 := by
  decide +kernel

theorem coreCheck825_91 :
    ∀ c : Fin 1, (coreChunks825_91 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 91)) = true := by
  decide +kernel
#print axioms coreFlatten825_91
#print axioms coreCheck825_91
end Erdos883Verified
