import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_18 :
    (List.ofFn coreChunks284_18).flatten =
      (coreData284.take (coreResources284 18).q).drop 49 := by
  decide +kernel

theorem coreCheck284_18 :
    ∀ c : Fin 1, (coreChunks284_18 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 18)) = true := by
  decide +kernel
#print axioms coreFlatten284_18
#print axioms coreCheck284_18
end Erdos883Verified
