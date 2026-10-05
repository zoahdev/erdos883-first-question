import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_33 :
    (List.ofFn coreChunks825_33).flatten =
      (coreData825.take (coreResources825 33).q).drop 172 := by
  decide +kernel

theorem coreCheck825_33 :
    ∀ c : Fin 1, (coreChunks825_33 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 33)) = true := by
  decide +kernel
#print axioms coreFlatten825_33
#print axioms coreCheck825_33
end Erdos883Verified
