import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_24 :
    (List.ofFn coreChunks284_24).flatten =
      (coreData284.take (coreResources284 24).q).drop 56 := by
  decide +kernel

theorem coreCheck284_24 :
    ∀ c : Fin 1, (coreChunks284_24 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 24)) = true := by
  decide +kernel
#print axioms coreFlatten284_24
#print axioms coreCheck284_24
end Erdos883Verified
