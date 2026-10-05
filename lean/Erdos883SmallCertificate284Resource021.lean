import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_21 :
    (List.ofFn coreChunks284_21).flatten =
      (coreData284.take (coreResources284 21).q).drop 53 := by
  decide +kernel

theorem coreCheck284_21 :
    ∀ c : Fin 1, (coreChunks284_21 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 21)) = true := by
  decide +kernel
#print axioms coreFlatten284_21
#print axioms coreCheck284_21
end Erdos883Verified
