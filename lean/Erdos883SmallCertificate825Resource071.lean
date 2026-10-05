import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_71 :
    (List.ofFn coreChunks825_71).flatten =
      (coreData825.take (coreResources825 71).q).drop 132 := by
  decide +kernel

theorem coreCheck825_71 :
    ∀ c : Fin 1, (coreChunks825_71 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 71)) = true := by
  decide +kernel
#print axioms coreFlatten825_71
#print axioms coreCheck825_71
end Erdos883Verified
