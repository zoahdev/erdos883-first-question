import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_1 :
    (List.ofFn coreChunks284_1).flatten =
      (coreData284.take (coreResources284 1).q).drop 31 := by
  decide +kernel

theorem coreCheck284_1 :
    ∀ c : Fin 1, (coreChunks284_1 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 1)) = true := by
  decide +kernel
#print axioms coreFlatten284_1
#print axioms coreCheck284_1
end Erdos883Verified
