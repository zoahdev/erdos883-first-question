import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_56 :
    (List.ofFn coreChunks284_56).flatten =
      (coreData284.take (coreResources284 56).q).drop 82 := by
  decide +kernel

theorem coreCheck284_56 :
    ∀ c : Fin 1, (coreChunks284_56 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 56)) = true := by
  decide +kernel
#print axioms coreFlatten284_56
#print axioms coreCheck284_56
end Erdos883Verified
