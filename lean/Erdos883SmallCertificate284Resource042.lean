import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_42 :
    (List.ofFn coreChunks284_42).flatten =
      (coreData284.take (coreResources284 42).q).drop 87 := by
  decide +kernel

theorem coreCheck284_42 :
    ∀ c : Fin 1, (coreChunks284_42 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 42)) = true := by
  decide +kernel
#print axioms coreFlatten284_42
#print axioms coreCheck284_42
end Erdos883Verified
