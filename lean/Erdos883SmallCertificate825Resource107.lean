import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_107 :
    (List.ofFn coreChunks825_107).flatten =
      (coreData825.take (coreResources825 107).q).drop 190 := by
  decide +kernel

theorem coreCheck825_107 :
    ∀ c : Fin 1, (coreChunks825_107 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 107)) = true := by
  decide +kernel
#print axioms coreFlatten825_107
#print axioms coreCheck825_107
end Erdos883Verified
