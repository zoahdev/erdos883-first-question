import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_25 :
    (List.ofFn coreChunks284_25).flatten =
      (coreData284.take (coreResources284 25).q).drop 58 := by
  decide +kernel

theorem coreCheck284_25 :
    ∀ c : Fin 1, (coreChunks284_25 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 25)) = true := by
  decide +kernel
#print axioms coreFlatten284_25
#print axioms coreCheck284_25
end Erdos883Verified
