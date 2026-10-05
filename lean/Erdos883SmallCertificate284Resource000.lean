import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_0 :
    (List.ofFn coreChunks284_0).flatten =
      (coreData284.take (coreResources284 0).q).drop 0 := by
  decide +kernel

theorem coreCheck284_0 :
    ∀ c : Fin 2, (coreChunks284_0 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 0)) = true := by
  decide +kernel
#print axioms coreFlatten284_0
#print axioms coreCheck284_0
end Erdos883Verified
