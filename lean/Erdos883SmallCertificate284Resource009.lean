import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_9 :
    (List.ofFn coreChunks284_9).flatten =
      (coreData284.take (coreResources284 9).q).drop 67 := by
  decide +kernel

theorem coreCheck284_9 :
    ∀ c : Fin 1, (coreChunks284_9 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 9)) = true := by
  decide +kernel
#print axioms coreFlatten284_9
#print axioms coreCheck284_9
end Erdos883Verified
