import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_26 :
    (List.ofFn coreChunks284_26).flatten =
      (coreData284.take (coreResources284 26).q).drop 60 := by
  decide +kernel

theorem coreCheck284_26 :
    ∀ c : Fin 1, (coreChunks284_26 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 26)) = true := by
  decide +kernel
#print axioms coreFlatten284_26
#print axioms coreCheck284_26
end Erdos883Verified
