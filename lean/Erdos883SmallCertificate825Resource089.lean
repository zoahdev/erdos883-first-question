import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_89 :
    (List.ofFn coreChunks825_89).flatten =
      (coreData825.take (coreResources825 89).q).drop 163 := by
  decide +kernel

theorem coreCheck825_89 :
    ∀ c : Fin 1, (coreChunks825_89 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 89)) = true := by
  decide +kernel
#print axioms coreFlatten825_89
#print axioms coreCheck825_89
end Erdos883Verified
