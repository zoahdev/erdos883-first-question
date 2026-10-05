import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_2 :
    (List.ofFn coreChunks284_2).flatten =
      (coreData284.take (coreResources284 2).q).drop 32 := by
  decide +kernel

theorem coreCheck284_2 :
    ∀ c : Fin 1, (coreChunks284_2 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 2)) = true := by
  decide +kernel
#print axioms coreFlatten284_2
#print axioms coreCheck284_2
end Erdos883Verified
