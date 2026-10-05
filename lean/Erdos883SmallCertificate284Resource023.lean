import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_23 :
    (List.ofFn coreChunks284_23).flatten =
      (coreData284.take (coreResources284 23).q).drop 55 := by
  decide +kernel

theorem coreCheck284_23 :
    ∀ c : Fin 1, (coreChunks284_23 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 23)) = true := by
  decide +kernel
#print axioms coreFlatten284_23
#print axioms coreCheck284_23
end Erdos883Verified
