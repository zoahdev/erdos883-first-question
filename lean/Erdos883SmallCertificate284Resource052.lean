import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_52 :
    (List.ofFn coreChunks284_52).flatten =
      (coreData284.take (coreResources284 52).q).drop 0 := by
  decide +kernel

theorem coreCheck284_52 :
    ∀ c : Fin 6, (coreChunks284_52 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 52)) = true := by
  decide +kernel
#print axioms coreFlatten284_52
#print axioms coreCheck284_52
end Erdos883Verified
