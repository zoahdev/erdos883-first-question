import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_88 :
    (List.ofFn coreChunks825_88).flatten =
      (coreData825.take (coreResources825 88).q).drop 160 := by
  decide +kernel

theorem coreCheck825_88 :
    ∀ c : Fin 1, (coreChunks825_88 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 88)) = true := by
  decide +kernel
#print axioms coreFlatten825_88
#print axioms coreCheck825_88
end Erdos883Verified
