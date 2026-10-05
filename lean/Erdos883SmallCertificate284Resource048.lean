import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_48 :
    (List.ofFn coreChunks284_48).flatten =
      (coreData284.take (coreResources284 48).q).drop 123 := by
  decide +kernel

theorem coreCheck284_48 :
    ∀ c : Fin 1, (coreChunks284_48 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 48)) = true := by
  decide +kernel
#print axioms coreFlatten284_48
#print axioms coreCheck284_48
end Erdos883Verified
