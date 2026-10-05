import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_86 :
    (List.ofFn coreChunks825_86).flatten =
      (coreData825.take (coreResources825 86).q).drop 155 := by
  decide +kernel

theorem coreCheck825_86 :
    ∀ c : Fin 1, (coreChunks825_86 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 86)) = true := by
  decide +kernel
#print axioms coreFlatten825_86
#print axioms coreCheck825_86
end Erdos883Verified
