import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_63 :
    (List.ofFn coreChunks825_63).flatten =
      (coreData825.take (coreResources825 63).q).drop 123 := by
  decide +kernel

theorem coreCheck825_63 :
    ∀ c : Fin 1, (coreChunks825_63 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 63)) = true := by
  decide +kernel
#print axioms coreFlatten825_63
#print axioms coreCheck825_63
end Erdos883Verified
