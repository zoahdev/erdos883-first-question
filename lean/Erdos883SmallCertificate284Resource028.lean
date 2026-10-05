import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_28 :
    (List.ofFn coreChunks284_28).flatten =
      (coreData284.take (coreResources284 28).q).drop 62 := by
  decide +kernel

theorem coreCheck284_28 :
    ∀ c : Fin 1, (coreChunks284_28 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 28)) = true := by
  decide +kernel
#print axioms coreFlatten284_28
#print axioms coreCheck284_28
end Erdos883Verified
