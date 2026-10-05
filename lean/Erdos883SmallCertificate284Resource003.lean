import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_3 :
    (List.ofFn coreChunks284_3).flatten =
      (coreData284.take (coreResources284 3).q).drop 38 := by
  decide +kernel

theorem coreCheck284_3 :
    ∀ c : Fin 2, (coreChunks284_3 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 3)) = true := by
  decide +kernel
#print axioms coreFlatten284_3
#print axioms coreCheck284_3
end Erdos883Verified
