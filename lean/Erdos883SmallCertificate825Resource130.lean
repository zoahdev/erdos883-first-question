import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_130 :
    (List.ofFn coreChunks825_130).flatten =
      (coreData825.take (coreResources825 130).q).drop 255 := by
  decide +kernel

theorem coreCheck825_130 :
    ∀ c : Fin 1, (coreChunks825_130 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 130)) = true := by
  decide +kernel
#print axioms coreFlatten825_130
#print axioms coreCheck825_130
end Erdos883Verified
