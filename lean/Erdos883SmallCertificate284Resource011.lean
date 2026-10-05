import Erdos883SmallCertificate284Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten284_11 :
    (List.ofFn coreChunks284_11).flatten =
      (coreData284.take (coreResources284 11).q).drop 69 := by
  decide +kernel

theorem coreCheck284_11 :
    ∀ c : Fin 1, (coreChunks284_11 c).all
      (coreResourceRowCheck 259 coreData284 (coreResources284 11)) = true := by
  decide +kernel
#print axioms coreFlatten284_11
#print axioms coreCheck284_11
end Erdos883Verified
