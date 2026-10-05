import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_39 :
    (List.ofFn coreChunks284_39).flatten =
      (coreData284.take (coreResources284 39).q).drop 80 := by
  decide +kernel

theorem coreCheck284_39 :
    ∀ c : Fin 1, (coreChunks284_39 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 39)) = true := by
  decide +kernel
#print axioms coreFlatten284_39
#print axioms coreCheck284_39
end Erdos883Verified
