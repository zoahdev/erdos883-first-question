import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_83 :
    (List.ofFn coreChunks825_83).flatten =
      (coreData825.take (coreResources825 83).q).drop 151 := by
  decide +kernel

theorem coreCheck825_83 :
    ∀ c : Fin 1, (coreChunks825_83 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 83)) = true := by
  decide +kernel
#print axioms coreFlatten825_83
#print axioms coreCheck825_83
end Erdos883Verified
