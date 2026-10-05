import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_104 :
    (List.ofFn coreChunks825_104).flatten =
      (coreData825.take (coreResources825 104).q).drop 185 := by
  decide +kernel

theorem coreCheck825_104 :
    ∀ c : Fin 1, (coreChunks825_104 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 104)) = true := by
  decide +kernel
#print axioms coreFlatten825_104
#print axioms coreCheck825_104
end Erdos883Verified
