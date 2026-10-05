import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_54 :
    (List.ofFn coreChunks284_54).flatten =
      (coreData284.take (coreResources284 54).q).drop 0 := by
  decide +kernel

theorem coreCheck284_54 :
    ∀ c : Fin 5, (coreChunks284_54 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 54)) = true := by
  decide +kernel
#print axioms coreFlatten284_54
#print axioms coreCheck284_54
end Erdos883Verified
