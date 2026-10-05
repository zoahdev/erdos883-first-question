import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_53 :
    (List.ofFn coreChunks284_53).flatten =
      (coreData284.take (coreResources284 53).q).drop 92 := by
  decide +kernel

theorem coreCheck284_53 :
    ∀ c : Fin 1, (coreChunks284_53 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 53)) = true := by
  decide +kernel
#print axioms coreFlatten284_53
#print axioms coreCheck284_53
end Erdos883Verified
