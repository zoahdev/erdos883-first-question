import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_12 :
    (List.ofFn coreChunks284_12).flatten =
      (coreData284.take (coreResources284 12).q).drop 0 := by
  decide +kernel

theorem coreCheck284_12 :
    ∀ c : Fin 2, (coreChunks284_12 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 12)) = true := by
  decide +kernel
#print axioms coreFlatten284_12
#print axioms coreCheck284_12
end Erdos883Verified
