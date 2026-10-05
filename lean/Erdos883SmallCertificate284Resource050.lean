import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_50 :
    (List.ofFn coreChunks284_50).flatten =
      (coreData284.take (coreResources284 50).q).drop 136 := by
  decide +kernel

theorem coreCheck284_50 :
    ∀ c : Fin 1, (coreChunks284_50 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 50)) = true := by
  decide +kernel
#print axioms coreFlatten284_50
#print axioms coreCheck284_50
end Erdos883Verified
