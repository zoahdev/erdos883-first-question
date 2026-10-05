import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_105 :
    (List.ofFn coreChunks825_105).flatten =
      (coreData825.take (coreResources825 105).q).drop 186 := by
  decide +kernel

theorem coreCheck825_105 :
    ∀ c : Fin 1, (coreChunks825_105 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 105)) = true := by
  decide +kernel
#print axioms coreFlatten825_105
#print axioms coreCheck825_105
end Erdos883Verified
