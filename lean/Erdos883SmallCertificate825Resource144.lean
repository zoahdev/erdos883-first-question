import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_144 :
    (List.ofFn coreChunks825_144).flatten =
      (coreData825.take (coreResources825 144).q).drop 347 := by
  decide +kernel

theorem coreCheck825_144 :
    ∀ c : Fin 1, (coreChunks825_144 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 144)) = true := by
  decide +kernel
#print axioms coreFlatten825_144
#print axioms coreCheck825_144
end Erdos883Verified
