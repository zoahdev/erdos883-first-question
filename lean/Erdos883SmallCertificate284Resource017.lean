import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_17 :
    (List.ofFn coreChunks284_17).flatten =
      (coreData284.take (coreResources284 17).q).drop 48 := by
  decide +kernel

theorem coreCheck284_17 :
    ∀ c : Fin 1, (coreChunks284_17 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 17)) = true := by
  decide +kernel
#print axioms coreFlatten284_17
#print axioms coreCheck284_17
end Erdos883Verified
