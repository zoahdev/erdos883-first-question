import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_37 :
    (List.ofFn coreChunks825_37).flatten =
      (coreData825.take (coreResources825 37).q).drop 177 := by
  decide +kernel

theorem coreCheck825_37 :
    ∀ c : Fin 1, (coreChunks825_37 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 37)) = true := by
  decide +kernel
#print axioms coreFlatten825_37
#print axioms coreCheck825_37
end Erdos883Verified
