import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_77 :
    (List.ofFn coreChunks825_77).flatten =
      (coreData825.take (coreResources825 77).q).drop 141 := by
  decide +kernel

theorem coreCheck825_77 :
    ∀ c : Fin 1, (coreChunks825_77 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 77)) = true := by
  decide +kernel
#print axioms coreFlatten825_77
#print axioms coreCheck825_77
end Erdos883Verified
