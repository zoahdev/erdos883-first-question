import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_47 :
    (List.ofFn coreChunks825_47).flatten =
      (coreData825.take (coreResources825 47).q).drop 187 := by
  decide +kernel

theorem coreCheck825_47 :
    ∀ c : Fin 1, (coreChunks825_47 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 47)) = true := by
  decide +kernel
#print axioms coreFlatten825_47
#print axioms coreCheck825_47
end Erdos883Verified
