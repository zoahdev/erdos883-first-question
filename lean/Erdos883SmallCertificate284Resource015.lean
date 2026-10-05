import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_15 :
    (List.ofFn coreChunks284_15).flatten =
      (coreData284.take (coreResources284 15).q).drop 44 := by
  decide +kernel

theorem coreCheck284_15 :
    ∀ c : Fin 1, (coreChunks284_15 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 15)) = true := by
  decide +kernel
#print axioms coreFlatten284_15
#print axioms coreCheck284_15
end Erdos883Verified
