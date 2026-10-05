import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_43 :
    (List.ofFn coreChunks284_43).flatten =
      (coreData284.take (coreResources284 43).q).drop 89 := by
  decide +kernel

theorem coreCheck284_43 :
    ∀ c : Fin 1, (coreChunks284_43 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 43)) = true := by
  decide +kernel
#print axioms coreFlatten284_43
#print axioms coreCheck284_43
end Erdos883Verified
