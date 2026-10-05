import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_45 :
    (List.ofFn coreChunks825_45).flatten =
      (coreData825.take (coreResources825 45).q).drop 185 := by
  decide +kernel

theorem coreCheck825_45 :
    ∀ c : Fin 1, (coreChunks825_45 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 45)) = true := by
  decide +kernel
#print axioms coreFlatten825_45
#print axioms coreCheck825_45
end Erdos883Verified
