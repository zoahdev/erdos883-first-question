import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_44 :
    (List.ofFn coreChunks825_44).flatten =
      (coreData825.take (coreResources825 44).q).drop 184 := by
  decide +kernel

theorem coreCheck825_44 :
    ∀ c : Fin 1, (coreChunks825_44 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 44)) = true := by
  decide +kernel
#print axioms coreFlatten825_44
#print axioms coreCheck825_44
end Erdos883Verified
