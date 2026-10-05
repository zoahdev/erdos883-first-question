import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_14 :
    (List.ofFn coreChunks284_14).flatten =
      (coreData284.take (coreResources284 14).q).drop 32 := by
  decide +kernel

theorem coreCheck284_14 :
    ∀ c : Fin 1, (coreChunks284_14 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 14)) = true := by
  decide +kernel
#print axioms coreFlatten284_14
#print axioms coreCheck284_14
end Erdos883Verified
