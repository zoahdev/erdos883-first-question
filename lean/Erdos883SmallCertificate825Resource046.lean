import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_46 :
    (List.ofFn coreChunks825_46).flatten =
      (coreData825.take (coreResources825 46).q).drop 186 := by
  decide +kernel

theorem coreCheck825_46 :
    ∀ c : Fin 1, (coreChunks825_46 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 46)) = true := by
  decide +kernel
#print axioms coreFlatten825_46
#print axioms coreCheck825_46
end Erdos883Verified
