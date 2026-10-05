import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_125 :
    (List.ofFn coreChunks825_125).flatten =
      (coreData825.take (coreResources825 125).q).drop 242 := by
  decide +kernel

theorem coreCheck825_125 :
    ∀ c : Fin 1, (coreChunks825_125 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 125)) = true := by
  decide +kernel
#print axioms coreFlatten825_125
#print axioms coreCheck825_125
end Erdos883Verified
