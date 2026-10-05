import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_22 :
    (List.ofFn coreChunks284_22).flatten =
      (coreData284.take (coreResources284 22).q).drop 54 := by
  decide +kernel

theorem coreCheck284_22 :
    ∀ c : Fin 1, (coreChunks284_22 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 22)) = true := by
  decide +kernel
#print axioms coreFlatten284_22
#print axioms coreCheck284_22
end Erdos883Verified
