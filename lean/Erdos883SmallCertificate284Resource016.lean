import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_16 :
    (List.ofFn coreChunks284_16).flatten =
      (coreData284.take (coreResources284 16).q).drop 45 := by
  decide +kernel

theorem coreCheck284_16 :
    ∀ c : Fin 1, (coreChunks284_16 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 16)) = true := by
  decide +kernel
#print axioms coreFlatten284_16
#print axioms coreCheck284_16
end Erdos883Verified
